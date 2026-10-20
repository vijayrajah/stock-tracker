package main

import (
	"bytes"
	"database/sql"
	"encoding/csv"
	"encoding/json"
	"fmt"
	"html/template"
	"io"
	"log"
	"math"
	"net/http"
	"sort"
	"strconv"
	"strings"
	"time"

	_ "modernc.org/sqlite"
)

// --- Domain Models & View Models ---

type CashFlow struct {
	Date   time.Time
	Amount float64
}

type StockHoldingViewModel struct {
	Symbol        string
	CleanSymbol   string
	Exchange      string
	TotalQty      float64
	AvgBuyPrice   float64
	CurrentPrice  float64
	InvestedValue float64
	CurrentValue  float64
	NominalPnL    float64
	RealPnL       float64
	XIRR          float64
}

type LotViewModel struct {
	TxID         int64
	Symbol       string
	CleanSymbol  string
	Exchange     string
	TradeDate    string
	RemainingQty float64
	BuyPrice     float64
	CurrentPrice float64
	NominalPnL   float64
	RealPnL      float64
	XIRR         float64
	Notes        string
}

type ClosedPositionViewModel struct {
	Symbol      string
	BuyDate     string
	SellDate    string
	HoldingDays int
	TaxType     string
	Quantity    float64
	BuyPrice    float64
	SellPrice   float64
	NominalPnL  float64
	RealPnL     float64
	Notes       string
}

type PortfolioSummary struct {
	TotalInvested float64
	CurrentValue  float64
	NominalPnL    float64
	RealPnL       float64
	OverallXIRR   float64
}

type DashboardData struct {
	Summary           PortfolioSummary
	RealizedSummary   RealizedSummary // <-- Added
	Holdings          []StockHoldingViewModel
	Lots              []LotViewModel
	ClosedTrades      []ClosedPositionViewModel // <-- Ensure this is present
	ChartLabelsJSON   template.JS
	ChartInvestedJSON template.JS
	ChartValueJSON    template.JS
}

type Transaction struct {
	ID        int64
	AssetID   int64
	Symbol    string
	Type      string
	TradeDate time.Time
	Quantity  float64
	Price     float64
	Fees      float64
	Notes     string
}

type OpenLot struct {
	TxID      int64
	Symbol    string
	TradeDate time.Time
	Qty       float64
	BuyPrice  float64
	Notes     string
}

type RealizedSummary struct {
	TotalRealizedNominal float64
	TotalRealizedReal    float64
	TotalSTCG            float64
	TotalLTCG            float64
}

// --- Date & Symbol Utilities ---

func parseFlexibleDate(raw string) time.Time {
	raw = strings.TrimSpace(raw)
	if raw == "" {
		return time.Now()
	}

	layouts := []string{
		"2006-01-02",
		"2006-01-02 15:04:05",
		time.RFC3339,
		"2006-01-02T15:04:05Z",
		"02-01-2006",
		"02/01/2006",
	}

	for _, layout := range layouts {
		if t, err := time.Parse(layout, raw); err == nil {
			return t
		}
	}

	if len(raw) >= 10 {
		if t, err := time.Parse("2006-01-02", raw[:10]); err == nil {
			return t
		}
	}

	return time.Now()
}

func normalizeSymbol(sym, exchange string) string {
	s := strings.ToUpper(strings.TrimSpace(sym))
	s = strings.TrimSuffix(strings.TrimSuffix(s, ".NS"), ".BO")
	if strings.ToUpper(exchange) == "BSE" {
		return s + ".BO"
	}
	return s + ".NS"
}

// --- Native Newton-Raphson XIRR Engine ---

// truncateToDay strips hours/minutes to prevent intraday fractional distortion
func truncateToDay(t time.Time) time.Time {
	return time.Date(t.Year(), t.Month(), t.Day(), 0, 0, 0, 0, time.UTC)
}

// xirrNPV computes the net present value for a given annual rate r
func xirrNPV(rate float64, cfs []CashFlow, startDate time.Time) float64 {
	npv := 0.0
	for _, cf := range cfs {
		days := cf.Date.Sub(startDate).Hours() / 24.0
		years := days / 365.0
		npv += cf.Amount / math.Pow(1.0+rate, years)
	}
	return npv
}

// xirrDeriv computes the first derivative of NPV with respect to r
func xirrDeriv(rate float64, cfs []CashFlow, startDate time.Time) float64 {
	d := 0.0
	for _, cf := range cfs {
		days := cf.Date.Sub(startDate).Hours() / 24.0
		years := days / 365.0
		d -= years * cf.Amount / math.Pow(1.0+rate, years+1.0)
	}
	return d
}

// CalculateXIRR uses a robust hybrid Newton-Raphson + Bisection fallback
// CalculateHoldingReturn calculates XIRR if held >= 30 days, or Absolute Return % if < 30 days
func CalculateHoldingReturn(cfs []CashFlow, totalInvested, currentValue float64) float64 {
	if totalInvested <= 0 || currentValue <= 0 || len(cfs) < 2 {
		if totalInvested > 0 {
			return ((currentValue - totalInvested) / totalInvested) * 100.0
		}
		return 0.0
	}

	startDate := truncateToDay(cfs[0].Date)
	endDate := truncateToDay(cfs[0].Date)

	for _, cf := range cfs {
		d := truncateToDay(cf.Date)
		if d.Before(startDate) {
			startDate = d
		}
		if d.After(endDate) {
			endDate = d
		}
	}

	days := endDate.Sub(startDate).Hours() / 24.0

	// Industry Standard: If holding span is under 30 days, annualized XIRR produces
	// distorted 1000%+ numbers or divides by zero. Return clean Absolute % instead.
	if days < 30 {
		return ((currentValue - totalInvested) / totalInvested) * 100.0
	}

	// Try Newton-Raphson XIRR
	guesses := []float64{0.10, 0.0, -0.15, 0.35, -0.40, 0.75}
	for _, guess := range guesses {
		r := guess
		for iter := 0; iter < 50; iter++ {
			f := xirrNPV(r, cfs, startDate)
			df := xirrDeriv(r, cfs, startDate)

			if math.Abs(f) < 1e-5 {
				return r * 100.0
			}
			if math.Abs(df) < 1e-9 {
				break
			}

			nextR := r - (f / df)
			if nextR <= -0.999 || nextR > 50.0 { // up to 5000% bounds
				break
			}
			if math.Abs(nextR-r) < 1e-6 {
				return nextR * 100.0
			}
			r = nextR
		}
	}

	// Fallback to Bisection
	low, high := -0.99, 50.0
	fLow := xirrNPV(low, cfs, startDate)
	fHigh := xirrNPV(high, cfs, startDate)

	if fLow*fHigh < 0 {
		for iter := 0; iter < 100; iter++ {
			mid := (low + high) / 2.0
			fMid := xirrNPV(mid, cfs, startDate)

			if math.Abs(fMid) < 1e-5 || (high-low)/2.0 < 1e-5 {
				return mid * 100.0
			}
			if (fLow > 0 && fMid > 0) || (fLow < 0 && fMid < 0) {
				low = mid
				fLow = fMid
			} else {
				high = mid
				fHigh = fMid
			}
		}
		return ((low + high) / 2.0) * 100.0
	}

	// Final Fallback: Absolute return % if XIRR cannot be determined
	return ((currentValue - totalInvested) / totalInvested) * 100.0
}

// --- Market Price Fetcher ---

func fetchYahooV8(symbol string) (float64, error) {
	url := fmt.Sprintf("https://query2.finance.yahoo.com/v8/finance/chart/%s?interval=1d&range=1d", symbol)

	client := &http.Client{Timeout: 8 * time.Second}
	req, err := http.NewRequest("GET", url, nil)
	if err != nil {
		return 0, err
	}

	req.Header.Set("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")
	req.Header.Set("Accept", "application/json")

	resp, err := client.Do(req)
	if err != nil {
		return 0, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return 0, fmt.Errorf("HTTP %d from Yahoo", resp.StatusCode)
	}

	var payload struct {
		Chart struct {
			Result []struct {
				Meta struct {
					RegularMarketPrice float64 `json:"regularMarketPrice"`
					ChartPreviousClose float64 `json:"chartPreviousClose"`
					PreviousClose      float64 `json:"previousClose"`
				} `json:"meta"`
			} `json:"result"`
			Error *struct {
				Description string `json:"description"`
			} `json:"error"`
		} `json:"chart"`
	}

	if err := json.NewDecoder(resp.Body).Decode(&payload); err != nil {
		return 0, err
	}

	if len(payload.Chart.Result) > 0 {
		meta := payload.Chart.Result[0].Meta
		if meta.RegularMarketPrice > 0 {
			return meta.RegularMarketPrice, nil
		}
		if meta.ChartPreviousClose > 0 {
			return meta.ChartPreviousClose, nil
		}
		if meta.PreviousClose > 0 {
			return meta.PreviousClose, nil
		}
	}

	return 0, fmt.Errorf("no valid price found in payload for %s", symbol)
}

func updatePriceForSymbol(db *sql.DB, symbol string) {
	price, err := fetchYahooV8(symbol)
	if err != nil {
		log.Printf("[FETCH FAILED] %s: %v", symbol, err)
		return
	}

	if price > 0 {
		_, err = db.Exec(`
			INSERT INTO daily_prices (symbol, price_date, close_price) 
			VALUES (?, date('now'), ?)
			ON CONFLICT(symbol, price_date) DO UPDATE SET close_price=excluded.close_price`,
			symbol, price,
		)
		if err != nil {
			log.Printf("[DB SAVE ERROR] %s: %v", symbol, err)
		} else {
			log.Printf("[PRICE UPDATED] %s -> ₹%.2f", symbol, price)
		}
	}
}

func updateAllPrices(db *sql.DB) {
	rows, err := db.Query("SELECT DISTINCT symbol FROM assets")
	if err != nil {
		log.Printf("Error fetching symbols: %v", err)
		return
	}

	var symbols []string
	for rows.Next() {
		var sym string
		if err := rows.Scan(&sym); err == nil {
			symbols = append(symbols, sym)
		}
	}
	rows.Close()

	for _, sym := range symbols {
		updatePriceForSymbol(db, sym)
	}
}

// --- Database & Portfolio Computation ---

func initDB(db *sql.DB) {
	queries := []string{
		`CREATE TABLE IF NOT EXISTS assets (
			id INTEGER PRIMARY KEY AUTOINCREMENT,
			symbol TEXT UNIQUE NOT NULL
		);`,
		`CREATE TABLE IF NOT EXISTS transactions (
			id INTEGER PRIMARY KEY AUTOINCREMENT,
			trade_id TEXT UNIQUE,
			asset_id INTEGER NOT NULL REFERENCES assets(id),
			type TEXT NOT NULL,
			trade_date DATE NOT NULL,
			quantity REAL NOT NULL,
			price REAL NOT NULL,
			fees REAL DEFAULT 0,
			notes TEXT
		);`,
		`CREATE TABLE IF NOT EXISTS daily_prices (
			symbol TEXT NOT NULL,
			price_date DATE NOT NULL,
			close_price REAL NOT NULL,
			PRIMARY KEY (symbol, price_date)
		);`,
		`CREATE TABLE IF NOT EXISTS cpi_index (
			period TEXT PRIMARY KEY,
			index_val REAL NOT NULL
		);`,
	}
	for _, q := range queries {
		if _, err := db.Exec(q); err != nil {
			log.Fatalf("Database setup failed: %v", err)
		}
	}

	_, _ = db.Exec(`ALTER TABLE transactions ADD COLUMN trade_id TEXT;`)
	_, _ = db.Exec(`CREATE UNIQUE INDEX IF NOT EXISTS idx_transactions_trade_id ON transactions(trade_id) WHERE trade_id IS NOT NULL;`)
}

func seedCPI(db *sql.DB) {
	cpiData := map[string]float64{
		"2023-01": 176.5, "2023-06": 181.4, "2023-12": 185.7,
		"2024-01": 186.2, "2024-06": 189.5, "2024-12": 193.1,
		"2025-01": 194.0, "2025-06": 196.2, "2025-12": 198.5,
		"2026-01": 199.2, "2026-06": 201.0, "2026-10": 202.5,
	}
	for period, val := range cpiData {
		_, _ = db.Exec(`INSERT OR IGNORE INTO cpi_index (period, index_val) VALUES (?, ?)`, period, val)
	}
}

func computePortfolio(db *sql.DB) ([]StockHoldingViewModel, []LotViewModel, []ClosedPositionViewModel, PortfolioSummary, RealizedSummary) {
	// 1. CPI Table
	cpiMap := make(map[string]float64)
	latestCPI := 202.5
	cRows, _ := db.Query("SELECT period, index_val FROM cpi_index ORDER BY period ASC")
	if cRows != nil {
		for cRows.Next() {
			var p string
			var v float64
			if err := cRows.Scan(&p, &v); err == nil {
				cpiMap[p] = v
				latestCPI = v
			}
		}
		cRows.Close()
	}

	// 2. Latest Prices
	priceMap := make(map[string]float64)
	pRows, _ := db.Query("SELECT symbol, close_price FROM daily_prices ORDER BY price_date DESC, rowid DESC")
	if pRows != nil {
		for pRows.Next() {
			var sym string
			var p float64
			if err := pRows.Scan(&sym, &p); err == nil {
				if _, exists := priceMap[sym]; !exists {
					priceMap[sym] = p
				}
			}
		}
		pRows.Close()
	}

	// 3. Transactions & FIFO Matching
	tRows, err := db.Query(`
		SELECT t.id, t.asset_id, a.symbol, t.type, 
		       COALESCE(t.trade_date, '') AS trade_date, 
		       t.quantity, t.price, t.fees, COALESCE(t.notes, '')
		FROM transactions t
		JOIN assets a ON t.asset_id = a.id
		ORDER BY t.trade_date ASC, t.id ASC
	`)
	if err != nil {
		return nil, nil, nil, PortfolioSummary{}, RealizedSummary{}
	}
	defer tRows.Close()

	assetLots := make(map[string][]OpenLot)
	var portfolioCashFlows []CashFlow
	var closedTrades []ClosedPositionViewModel
	var realizedSummary RealizedSummary
	stockCashFlows := make(map[string][]CashFlow)

	for tRows.Next() {
		var tx Transaction
		var dStr string
		if err := tRows.Scan(&tx.ID, &tx.AssetID, &tx.Symbol, &tx.Type, &dStr, &tx.Quantity, &tx.Price, &tx.Fees, &tx.Notes); err != nil {
			continue
		}
		tx.TradeDate = parseFlexibleDate(dStr)
		totalAmount := (tx.Quantity * tx.Price) + tx.Fees

		if tx.Type == "BUY" {
			portfolioCashFlows = append(portfolioCashFlows, CashFlow{
				Date:   tx.TradeDate,
				Amount: -totalAmount,
			})
			// Also record outflow for the specific stock's overall XIRR:
			stockCashFlows[tx.Symbol] = append(stockCashFlows[tx.Symbol], CashFlow{
				Date:   tx.TradeDate,
				Amount: -totalAmount,
			})

			assetLots[tx.Symbol] = append(assetLots[tx.Symbol], OpenLot{
				TxID:      tx.ID,
				Symbol:    tx.Symbol,
				TradeDate: tx.TradeDate,
				Qty:       tx.Quantity,
				BuyPrice:  tx.Price,
				Notes:     tx.Notes,
			})
		} else if tx.Type == "SELL" {
			sellProceeds := (tx.Quantity * tx.Price) - tx.Fees
			portfolioCashFlows = append(portfolioCashFlows, CashFlow{
				Date:   tx.TradeDate,
				Amount: sellProceeds,
			})
			// Also record inflow for the specific stock's overall XIRR:
			stockCashFlows[tx.Symbol] = append(stockCashFlows[tx.Symbol], CashFlow{
				Date:   tx.TradeDate,
				Amount: sellProceeds,
			})

			qtyToSell := tx.Quantity
			lots := assetLots[tx.Symbol]
			for i := range lots {
				if lots[i].Qty <= 0 {
					continue
				}
				matchedQty := 0.0
				if lots[i].Qty <= qtyToSell {
					matchedQty = lots[i].Qty
					lots[i].Qty = 0
				} else {
					matchedQty = qtyToSell
					lots[i].Qty -= matchedQty
				}
				qtyToSell -= matchedQty

				// Holding duration & tax bracket (> 365 days is LTCG)
				holdingDays := int(tx.TradeDate.Sub(lots[i].TradeDate).Hours() / 24)
				taxType := "STCG"
				if holdingDays > 365 {
					taxType = "LTCG"
				}

				// Inflation indexing between buy and sell month
				buyPeriod := lots[i].TradeDate.Format("2006-01")
				sellPeriod := tx.TradeDate.Format("2006-01")
				buyCPI := cpiMap[buyPeriod]
				if buyCPI == 0 {
					buyCPI = latestCPI
				}
				sellCPI := cpiMap[sellPeriod]
				if sellCPI == 0 {
					sellCPI = latestCPI
				}
				cpiFactor := 1.0
				if buyCPI > 0 && sellCPI > 0 {
					cpiFactor = sellCPI / buyCPI
				}

				nominalCost := matchedQty * lots[i].BuyPrice
				saleRevenue := matchedQty * tx.Price
				nominalPnL := saleRevenue - nominalCost
				realCost := nominalCost * cpiFactor
				realPnL := saleRevenue - realCost

				realizedSummary.TotalRealizedNominal += nominalPnL
				realizedSummary.TotalRealizedReal += realPnL
				if taxType == "LTCG" {
					realizedSummary.TotalLTCG += nominalPnL
				} else {
					realizedSummary.TotalSTCG += nominalPnL
				}

				tradeNotes := lots[i].Notes
				if tx.Notes != "" && tx.Notes != "Imported from Kite" {
					if tradeNotes != "" {
						tradeNotes += " | Exit: " + tx.Notes
					} else {
						tradeNotes = "Exit: " + tx.Notes
					}
				}

				closedTrades = append(closedTrades, ClosedPositionViewModel{
					Symbol:      tx.Symbol,
					BuyDate:     lots[i].TradeDate.Format("02 Jan 2006"),
					SellDate:    tx.TradeDate.Format("02 Jan 2006"),
					HoldingDays: holdingDays,
					TaxType:     taxType,
					Quantity:    matchedQty,
					BuyPrice:    lots[i].BuyPrice,
					SellPrice:   tx.Price,
					NominalPnL:  nominalPnL,
					RealPnL:     realPnL,
					Notes:       tradeNotes,
				})

				if qtyToSell <= 0 {
					break
				}
			}
			assetLots[tx.Symbol] = lots
		}
	}

	// 4. Open Lots & Aggregated Holdings
	var detailedLots []LotViewModel
	holdingsMap := make(map[string]*StockHoldingViewModel)

	var summary PortfolioSummary
	now := time.Now()

	for symbol, lots := range assetLots {
		for _, lot := range lots {
			if lot.Qty <= 0 {
				continue
			}

			cleanSym := strings.TrimSuffix(strings.TrimSuffix(symbol, ".NS"), ".BO")
			exchange := "NSE"
			if strings.HasSuffix(symbol, ".BO") {
				exchange = "BSE"
			}

			effectivePrice := priceMap[symbol]
			if effectivePrice == 0 {
				effectivePrice = lot.BuyPrice
			}

			cost := lot.Qty * lot.BuyPrice
			currVal := lot.Qty * effectivePrice
			nominalPnL := currVal - cost

			buyPeriod := lot.TradeDate.Format("2006-01")
			cpiAtBuy := cpiMap[buyPeriod]
			if cpiAtBuy == 0 {
				cpiAtBuy = latestCPI
			}
			cpiFactor := latestCPI / cpiAtBuy
			realCost := cost * cpiFactor
			realPnL := currVal - realCost

			// Lot-level return:
			lotCfs := []CashFlow{
				{Date: lot.TradeDate, Amount: -cost},
				{Date: now, Amount: currVal},
			}
			lotReturn := CalculateHoldingReturn(lotCfs, cost, currVal)

			detailedLots = append(detailedLots, LotViewModel{
				TxID:         lot.TxID,
				Symbol:       symbol,
				CleanSymbol:  cleanSym,
				Exchange:     exchange,
				TradeDate:    lot.TradeDate.Format("02 Jan 2006"),
				RemainingQty: lot.Qty,
				BuyPrice:     lot.BuyPrice,
				CurrentPrice: effectivePrice,
				NominalPnL:   nominalPnL,
				RealPnL:      realPnL,
				XIRR:         lotReturn,
				Notes:        lot.Notes,
			})

			h, exists := holdingsMap[symbol]
			if !exists {
				h = &StockHoldingViewModel{
					Symbol:       symbol,
					CleanSymbol:  cleanSym,
					Exchange:     exchange,
					CurrentPrice: effectivePrice,
				}
				holdingsMap[symbol] = h
			}
			h.TotalQty += lot.Qty
			h.InvestedValue += cost
			h.CurrentValue += currVal
			h.NominalPnL += nominalPnL
			h.RealPnL += realPnL

			stockCashFlows[symbol] = append(stockCashFlows[symbol], CashFlow{
				Date:   lot.TradeDate,
				Amount: -cost,
			})

			summary.TotalInvested += cost
			summary.CurrentValue += currVal
			summary.NominalPnL += nominalPnL
			summary.RealPnL += realPnL
		}
	}

	var consolidatedHoldings []StockHoldingViewModel
	for sym, h := range holdingsMap {
		if h.TotalQty > 0 {
			h.AvgBuyPrice = h.InvestedValue / h.TotalQty

			cfs := append([]CashFlow{}, stockCashFlows[sym]...)
			cfs = append(cfs, CashFlow{
				Date:   truncateToDay(now),
				Amount: h.CurrentValue,
			})

			// Consolidated Stock Return:
			h.XIRR = CalculateHoldingReturn(cfs, h.InvestedValue, h.CurrentValue)
			consolidatedHoldings = append(consolidatedHoldings, *h)
		}
	}

	if summary.CurrentValue > 0 {
		portfolioCashFlows = append(portfolioCashFlows, CashFlow{
			Date:   truncateToDay(now),
			Amount: summary.CurrentValue,
		})
	}
	// Overall Portfolio Return:
	summary.OverallXIRR = CalculateHoldingReturn(portfolioCashFlows, summary.TotalInvested, summary.CurrentValue)

	sort.Slice(consolidatedHoldings, func(i, j int) bool {
		return consolidatedHoldings[i].CleanSymbol < consolidatedHoldings[j].CleanSymbol
	})

	sort.Slice(detailedLots, func(i, j int) bool {
		t1, _ := time.Parse("02 Jan 2006", detailedLots[i].TradeDate)
		t2, _ := time.Parse("02 Jan 2006", detailedLots[j].TradeDate)
		return t1.After(t2)
	})

	sort.Slice(closedTrades, func(i, j int) bool {
		t1, _ := time.Parse("02 Jan 2006", closedTrades[i].SellDate)
		t2, _ := time.Parse("02 Jan 2006", closedTrades[j].SellDate)
		return t1.After(t2)
	})

	return consolidatedHoldings, detailedLots, closedTrades, summary, realizedSummary
}

func computePortfolioTimeline(db *sql.DB, latestLots []LotViewModel, currentSummary PortfolioSummary) (template.JS, template.JS, template.JS) {
	rows, err := db.Query(`
		SELECT trade_date, type, quantity, price 
		FROM transactions 
		ORDER BY trade_date ASC
	`)
	if err != nil {
		return "[]", "[]", "[]"
	}
	defer rows.Close()

	var dates []string
	var investedSeries []float64
	var valueSeries []float64

	runningInvested := 0.0

	for rows.Next() {
		var dStr, txType string
		var qty, price float64
		if err := rows.Scan(&dStr, &txType, &qty, &price); err == nil {
			t := parseFlexibleDate(dStr)
			formattedDate := t.Format("02 Jan 2006")

			amount := qty * price
			if txType == "BUY" {
				runningInvested += amount
			} else {
				runningInvested -= amount
				if runningInvested < 0 {
					runningInvested = 0
				}
			}

			dates = append(dates, formattedDate)
			investedSeries = append(investedSeries, runningInvested)
			valueSeries = append(valueSeries, runningInvested)
		}
	}

	todayStr := time.Now().Format("02 Jan 2006")
	if len(dates) == 0 || dates[len(dates)-1] != todayStr {
		dates = append(dates, todayStr)
		investedSeries = append(investedSeries, currentSummary.TotalInvested)
		valueSeries = append(valueSeries, currentSummary.CurrentValue)
	} else {
		valueSeries[len(valueSeries)-1] = currentSummary.CurrentValue
		investedSeries[len(investedSeries)-1] = currentSummary.TotalInvested
	}

	labelsJSON, _ := json.Marshal(dates)
	invJSON, _ := json.Marshal(investedSeries)
	valJSON, _ := json.Marshal(valueSeries)

	return template.JS(labelsJSON), template.JS(invJSON), template.JS(valJSON)
}

func parseZerodhaCSV(db *sql.DB, r io.Reader) (int, error) {
	reader := csv.NewReader(r)
	reader.TrimLeadingSpace = true
	headers, err := reader.Read()
	if err != nil {
		return 0, err
	}

	colMap := make(map[string]int)
	for i, h := range headers {
		colMap[strings.ToLower(strings.TrimSpace(h))] = i
	}

	tx, err := db.Begin()
	if err != nil {
		return 0, err
	}
	defer tx.Rollback()

	stmtInsertTx, err := tx.Prepare(`
		INSERT OR IGNORE INTO transactions (trade_id, asset_id, type, trade_date, quantity, price, notes)
		VALUES (?, ?, ?, ?, ?, ?, 'Imported from Kite')
	`)
	if err != nil {
		return 0, err
	}
	defer stmtInsertTx.Close()

	stmtGetAsset, _ := tx.Prepare("SELECT id FROM assets WHERE symbol = ?")
	defer stmtGetAsset.Close()

	stmtInsertAsset, _ := tx.Prepare("INSERT INTO assets (symbol) VALUES (?)")
	defer stmtInsertAsset.Close()

	importedCount := 0

	for {
		rec, err := reader.Read()
		if err == io.EOF {
			break
		}
		if err != nil {
			return importedCount, err
		}

		rawSym := strings.TrimSpace(rec[colMap["symbol"]])
		tradeType := strings.ToUpper(strings.TrimSpace(rec[colMap["trade_type"]]))
		rawDate := strings.TrimSpace(rec[colMap["trade_date"]])
		qty, _ := strconv.ParseFloat(strings.TrimSpace(rec[colMap["quantity"]]), 64)
		price, _ := strconv.ParseFloat(strings.TrimSpace(rec[colMap["price"]]), 64)

		if qty <= 0 || price <= 0 {
			continue
		}

		tradeID := ""
		if idx, ok := colMap["trade_id"]; ok && idx < len(rec) {
			tradeID = strings.TrimSpace(rec[idx])
		}
		if tradeID == "" {
			tradeID = fmt.Sprintf("%s-%s-%s-%.4f-%.2f", rawSym, tradeType, rawDate, qty, price)
		}

		exchange := "NSE"
		if idx, ok := colMap["exchange"]; ok && idx < len(rec) {
			if ex := strings.ToUpper(strings.TrimSpace(rec[idx])); ex != "" {
				exchange = ex
			}
		}

		qualifiedSymbol := normalizeSymbol(rawSym, exchange)
		parsedDate := parseFlexibleDate(rawDate)
		tradeDate := parsedDate.Format("2006-01-02")

		var assetID int64
		err = stmtGetAsset.QueryRow(qualifiedSymbol).Scan(&assetID)
		if err == sql.ErrNoRows {
			res, err := stmtInsertAsset.Exec(qualifiedSymbol)
			if err != nil {
				return importedCount, err
			}
			assetID, _ = res.LastInsertId()
		}

		res, err := stmtInsertTx.Exec(tradeID, assetID, tradeType, tradeDate, qty, price)
		if err != nil {
			continue
		}

		if rowsAffected, _ := res.RowsAffected(); rowsAffected > 0 {
			importedCount++
		}
	}

	return importedCount, tx.Commit()
}

// --- Main HTTP Application ---

func main() {
	db, err := sql.Open("sqlite", "tracker.db?_pragma=busy_timeout(5000)&_pragma=journal_mode(WAL)")
	if err != nil {
		log.Fatalf("Failed to open SQLite database: %v", err)
	}
	defer db.Close()

	db.SetMaxOpenConns(1)

	initDB(db)
	seedCPI(db)

	tmpl := template.Must(template.ParseFiles("index.html"))

	fs := http.FileServer(http.Dir("static"))
	http.Handle("/static/", http.StripPrefix("/static/", fs))

	http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/" {
			http.NotFound(w, r)
			return
		}

		holdings, lots, closedTrades, summary, realizedSummary := computePortfolio(db)
		chartDates, chartInv, chartVal := computePortfolioTimeline(db, lots, summary)

		data := DashboardData{
			Summary:           summary,
			RealizedSummary:   realizedSummary, // Populated here
			Holdings:          holdings,
			Lots:              lots,
			ClosedTrades:      closedTrades, // Populated here
			ChartLabelsJSON:   chartDates,
			ChartInvestedJSON: chartInv,
			ChartValueJSON:    chartVal,
		}

		var buf bytes.Buffer
		if err := tmpl.Execute(&buf, data); err != nil {
			log.Printf("[TEMPLATE ERROR] Failed to render index.html: %v", err)
			http.Error(w, fmt.Sprintf("Template Error: %v", err), http.StatusInternalServerError)
			return
		}

		w.Header().Set("Content-Type", "text/html; charset=utf-8")
		buf.WriteTo(w)
	})

	http.HandleFunc("/api/transactions", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		rawSymbol := strings.TrimSpace(r.FormValue("symbol"))
		exchange := strings.TrimSpace(r.FormValue("exchange"))
		txType := strings.ToUpper(strings.TrimSpace(r.FormValue("type")))
		tradeDateRaw := strings.TrimSpace(r.FormValue("trade_date"))
		notes := strings.TrimSpace(r.FormValue("notes"))

		var qty, price float64
		fmt.Sscanf(r.FormValue("quantity"), "%f", &qty)
		fmt.Sscanf(r.FormValue("price"), "%f", &price)

		symbol := normalizeSymbol(rawSymbol, exchange)
		parsedDate := parseFlexibleDate(tradeDateRaw)
		formattedDate := parsedDate.Format("2006-01-02")

		var assetID int64
		err := db.QueryRow("SELECT id FROM assets WHERE symbol = ?", symbol).Scan(&assetID)
		if err == sql.ErrNoRows {
			res, err := db.Exec("INSERT INTO assets (symbol) VALUES (?)", symbol)
			if err != nil {
				http.Error(w, err.Error(), http.StatusInternalServerError)
				return
			}
			assetID, _ = res.LastInsertId()
		}

		_, err = db.Exec(`
			INSERT INTO transactions (asset_id, type, trade_date, quantity, price, notes)
			VALUES (?, ?, ?, ?, ?, ?)`,
			assetID, txType, formattedDate, qty, price, notes,
		)
		if err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}

		updatePriceForSymbol(db, symbol)
		http.Redirect(w, r, "/", http.StatusSeeOther)
	})

	http.HandleFunc("/api/import-csv", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		file, _, err := r.FormFile("tradebook_csv")
		if err != nil {
			http.Error(w, "File upload error", http.StatusBadRequest)
			return
		}
		defer file.Close()

		count, err := parseZerodhaCSV(db, file)
		if err != nil {
			http.Error(w, fmt.Sprintf("CSV Parsing failed: %v", err), http.StatusInternalServerError)
			return
		}

		go updateAllPrices(db)
		w.Header().Set("HX-Refresh", "true")
		w.Write([]byte(fmt.Sprintf("Imported %d new trades successfully", count)))
	})

	http.HandleFunc("/api/prices/refresh-all", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		updateAllPrices(db)
		w.Header().Set("HX-Refresh", "true")
		w.WriteHeader(http.StatusOK)
	})

	http.HandleFunc("/api/override-price", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		rawSymbol := strings.TrimSpace(r.FormValue("symbol"))
		exchange := strings.TrimSpace(r.FormValue("exchange"))
		symbol := normalizeSymbol(rawSymbol, exchange)

		var price float64
		fmt.Sscanf(r.FormValue("price"), "%f", &price)

		_, _ = db.Exec(`
			INSERT INTO daily_prices (symbol, price_date, close_price) 
			VALUES (?, date('now'), ?)
			ON CONFLICT(symbol, price_date) DO UPDATE SET close_price=excluded.close_price`,
			symbol, price,
		)

		http.Redirect(w, r, "/", http.StatusSeeOther)
	})

	log.Println("Portfolio Tracker live on http://localhost:8080")
	if err := http.ListenAndServe(":8080", nil); err != nil {
		log.Fatalf("Server stopped: %v", err)
	}
}
