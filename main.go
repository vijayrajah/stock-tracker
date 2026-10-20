package main

import (
	"database/sql"
	"embed"
	"encoding/csv"
	"encoding/json"
	"fmt"
	"html/template"
	"io"
	"log"
	"net/http"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"time"

	_ "modernc.org/sqlite"
)

//go:embed index.html
var templateFS embed.FS

//go:embed static/*
var staticFS embed.FS

// Models
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

type LotViewModel struct {
	TxID         int64
	Symbol       string
	TradeDate    string
	RemainingQty float64
	BuyPrice     float64
	CurrentPrice float64
	NominalPnL   float64
	RealPnL      float64
	Notes        string
}

type PortfolioSummary struct {
	TotalInvested float64
	CurrentValue  float64
	NominalPnL    float64
	RealPnL       float64
}

type NotePayload struct {
	TxID  int64
	Notes string
}

type ClosedPositionViewModel struct {
	Symbol      string
	BuyDate     string
	SellDate    string
	HoldingDays int
	TaxType     string // "LTCG" (>365 days) or "STCG" (<=365 days)
	Quantity    float64
	BuyPrice    float64
	SellPrice   float64
	NominalPnL  float64
	RealPnL     float64
	Notes       string
}

type RealizedSummary struct {
	TotalRealizedNominal float64
	TotalRealizedReal    float64
	TotalSTCG            float64
	TotalLTCG            float64
}

// Extend DashboardData to include closed trades
type DashboardData struct {
	Summary         PortfolioSummary
	RealizedSummary RealizedSummary
	Lots            []LotViewModel
	ClosedTrades    []ClosedPositionViewModel
}

// MoSPI CPI Dataset (2020-2025)
var defaultCPIData = map[string]float64{
	"2020-01": 150.2, "2020-02": 149.1, "2020-03": 148.6, "2020-04": 151.0,
	"2020-05": 151.5, "2020-06": 153.2, "2020-07": 155.0, "2020-08": 155.8,
	"2020-09": 157.6, "2020-10": 158.4, "2020-11": 158.9, "2020-12": 157.3,
	"2021-01": 156.3, "2021-02": 156.6, "2021-03": 156.8, "2021-04": 157.8,
	"2021-05": 160.4, "2021-06": 161.3, "2021-07": 162.5, "2021-08": 162.9,
	"2021-09": 163.2, "2021-10": 165.5, "2021-11": 166.7, "2021-12": 166.2,
	"2022-01": 165.7, "2022-02": 166.1, "2022-03": 167.7, "2022-04": 170.1,
	"2022-05": 171.7, "2022-06": 172.6, "2022-07": 173.4, "2022-08": 174.3,
	"2022-09": 175.3, "2022-10": 177.1, "2022-11": 176.7, "2022-12": 175.7,
	"2023-01": 176.5, "2023-02": 176.8, "2023-03": 177.2, "2023-04": 178.6,
	"2023-05": 179.8, "2023-06": 181.3, "2023-07": 187.6, "2023-08": 186.6,
	"2023-09": 184.2, "2023-10": 186.3, "2023-11": 187.4, "2023-12": 186.2,
	"2024-01": 185.7, "2024-02": 185.9, "2024-03": 185.8, "2024-04": 186.7,
	"2024-05": 187.6, "2024-06": 189.7, "2024-07": 192.3, "2024-08": 193.0,
	"2024-09": 193.3, "2024-10": 196.8, "2024-11": 196.5, "2024-12": 195.4,
	"2025-01": 194.0, "2025-02": 193.8, "2025-03": 194.2, "2025-04": 194.6,
	"2025-05": 195.4, "2025-06": 196.2, "2025-07": 196.1, "2025-08": 197.0,
	"2025-09": 197.1, "2025-10": 197.3, "2025-11": 197.9, "2025-12": 198.0,
}

func main() {
	db, err := sql.Open("sqlite", "tracker.db?_pragma=busy_timeout(5000)&_pragma=journal_mode(WAL)")
	if err != nil {
		log.Fatalf("Failed to open SQLite database: %v", err)
	}
	defer db.Close()

	initDB(db)
	seedCPI(db)

	// Scheduled daily price update routine
	go func() {
		for {
			updateAllPrices(db)
			time.Sleep(24 * time.Hour)
		}
	}()

	tmpl := template.Must(template.ParseFS(templateFS, "index.html"))

	// 1. Serve embedded static files (CSS & JS)
	http.Handle("/static/", http.FileServer(http.FS(staticFS)))

	// Dashboard page
	http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		lots, summary := computePortfolio(db)
		data := DashboardData{Summary: summary, Lots: lots}
		if err := tmpl.Execute(w, data); err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
		}
	})

	// Live search filter endpoint
	http.HandleFunc("/api/portfolio/search", func(w http.ResponseWriter, r *http.Request) {
		q := strings.ToLower(strings.TrimSpace(r.URL.Query().Get("q")))
		allLots, _ := computePortfolio(db)

		var filtered []LotViewModel
		for _, lot := range allLots {
			if q == "" || strings.Contains(strings.ToLower(lot.Symbol), q) || strings.Contains(strings.ToLower(lot.Notes), q) {
				filtered = append(filtered, lot)
			}
		}

		w.Header().Set("Content-Type", "text/html")
		_ = tmpl.ExecuteTemplate(w, "table_rows", filtered)
	})

	// Manual transaction creation
	http.HandleFunc("/api/transactions", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		symbol := strings.ToUpper(strings.TrimSpace(r.FormValue("symbol")))
		// Auto-normalize: If user typed "TCS", turn it into "TCS.NS"
		if !strings.HasSuffix(symbol, ".NS") && !strings.HasSuffix(symbol, ".BO") {
			symbol = symbol + ".NS"
		}

		txType := strings.ToUpper(strings.TrimSpace(r.FormValue("type")))
		tradeDateRaw := strings.TrimSpace(r.FormValue("trade_date"))
		notes := strings.TrimSpace(r.FormValue("notes"))

		var qty, price float64
		fmt.Sscanf(r.FormValue("quantity"), "%f", &qty)
		fmt.Sscanf(r.FormValue("price"), "%f", &price)

		parsedDate := parseFlexibleDate(tradeDateRaw)
		formattedDate := parsedDate.Format("2006-01-02")

		// Ensure asset exists
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

		// Insert transaction
		_, err = db.Exec(`
        INSERT INTO transactions (asset_id, type, trade_date, quantity, price, notes)
        VALUES (?, ?, ?, ?, ?, ?)`,
			assetID, txType, formattedDate, qty, price, notes,
		)
		if err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}

		// Fetch the price synchronously BEFORE redirecting so the table immediately has it
		updatePriceForSymbol(db, symbol)

		http.Redirect(w, r, "/", http.StatusSeeOther)
	})

	// Zerodha Kite Tradebook CSV Upload
	http.HandleFunc("/api/upload/zerodha", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		r.Body = http.MaxBytesReader(w, r.Body, 10<<20)
		file, _, err := r.FormFile("tradebook_csv")
		if err != nil {
			http.Error(w, "Invalid upload: "+err.Error(), http.StatusBadRequest)
			return
		}
		defer file.Close()

		count, err := parseZerodhaCSV(db, file)
		if err != nil {
			w.Header().Set("Content-Type", "text/html")
			fmt.Fprintf(w, "<p style='color: red;'>Error parsing CSV: %v</p>", err)
			return
		}

		go updateAllPrices(db)

		w.Header().Set("Content-Type", "text/html")
		fmt.Fprintf(w, "<p style='color: green;'>Successfully imported %d trades! Refreshing...</p><script>setTimeout(() => location.reload(), 1000);</script>", count)
	})

	// Inline Note Editing API
	noteReadTmpl := template.Must(template.New("read").Parse(`
		<td id="note-cell-{{ .TxID }}" hx-get="/api/transactions/{{ .TxID }}/notes/edit" hx-trigger="click" hx-swap="outerHTML" style="cursor: pointer;">
		  {{ if .Notes }}<small>{{ .Notes }}</small>{{ else }}<small class="muted" style="font-style: italic;">+ Add notes</small>{{ end }}
		  <span style="font-size: 0.75rem; opacity: 0.5; margin-left: 4px;">✏️</span>
		</td>
	`))

	noteEditTmpl := template.Must(template.New("edit").Parse(`
		<td id="note-cell-{{ .TxID }}" style="min-width: 220px;">
		  <form hx-post="/api/transactions/{{ .TxID }}/notes" hx-target="#note-cell-{{ .TxID }}" hx-swap="outerHTML" style="margin: 0;">
		    <input type="text" name="notes" value="{{ .Notes }}" autofocus style="margin-bottom: 0.4rem; font-size: 0.85rem;" />
		    <div style="display: flex; gap: 0.4rem;">
		      <button type="submit" class="outline" style="padding: 2px 8px; font-size: 0.75rem;">Save</button>
		      <button type="button" class="secondary outline" hx-get="/api/transactions/{{ .TxID }}/notes" hx-target="#note-cell-{{ .TxID }}" hx-swap="outerHTML" style="padding: 2px 8px; font-size: 0.75rem;">Cancel</button>
		    </div>
		  </form>
		</td>
	`))

	http.HandleFunc("/api/transactions/", func(w http.ResponseWriter, r *http.Request) {
		path := strings.TrimPrefix(r.URL.Path, "/api/transactions/")
		parts := strings.Split(path, "/")
		if len(parts) < 2 || parts[1] != "notes" {
			http.NotFound(w, r)
			return
		}

		txID, _ := strconv.ParseInt(parts[0], 10, 64)
		w.Header().Set("Content-Type", "text/html")

		if len(parts) == 3 && parts[2] == "edit" && r.Method == http.MethodGet {
			var notes string
			_ = db.QueryRow("SELECT COALESCE(notes, '') FROM transactions WHERE id = ?", txID).Scan(&notes)
			noteEditTmpl.Execute(w, NotePayload{TxID: txID, Notes: notes})
			return
		}

		if r.Method == http.MethodPost {
			newNote := strings.TrimSpace(r.FormValue("notes"))
			db.Exec("UPDATE transactions SET notes = ? WHERE id = ?", newNote, txID)
			noteReadTmpl.Execute(w, NotePayload{TxID: txID, Notes: newNote})
			return
		}

		if r.Method == http.MethodGet {
			var notes string
			_ = db.QueryRow("SELECT COALESCE(notes, '') FROM transactions WHERE id = ?", txID).Scan(&notes)
			noteReadTmpl.Execute(w, NotePayload{TxID: txID, Notes: notes})
			return
		}
	})

	// Endpoint to refresh prices for all tracked assets on demand
	http.HandleFunc("/api/prices/refresh-all", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		// Run the price updater synchronously so we only refresh once done
		updateAllPrices(db)

		// HX-Refresh tells HTMX to refresh the entire dashboard,
		// immediately reflecting new market values and P&L cards
		w.Header().Set("HX-Refresh", "true")
		w.WriteHeader(http.StatusOK)
	})

	// Manual Overrides
	http.HandleFunc("/api/override-price", func(w http.ResponseWriter, r *http.Request) {
		if r.Method == http.MethodPost {
			symbol := strings.ToUpper(strings.TrimSpace(r.FormValue("symbol")))
			var price float64
			fmt.Sscanf(r.FormValue("price"), "%f", &price)
			db.Exec(`INSERT INTO daily_prices (symbol, price_date, close_price) 
			         VALUES (?, date('now'), ?)
			         ON CONFLICT(symbol, price_date) DO UPDATE SET close_price=excluded.close_price`, symbol, price)
			http.Redirect(w, r, "/", http.StatusSeeOther)
		}
	})

	http.HandleFunc("/api/cpi", func(w http.ResponseWriter, r *http.Request) {
		if r.Method == http.MethodPost {
			period := strings.TrimSpace(r.FormValue("period"))
			var val float64
			fmt.Sscanf(r.FormValue("index_val"), "%f", &val)
			db.Exec(`INSERT INTO cpi_index (period, index_val) VALUES (?, ?)
			         ON CONFLICT(period) DO UPDATE SET index_val=excluded.index_val`, period, val)
			http.Redirect(w, r, "/", http.StatusSeeOther)
		}
	})

	fmt.Println("Stock Tracker active at http://localhost:8080")
	log.Fatal(http.ListenAndServe(":8080", nil))
}

// Database Initialization
func initDB(db *sql.DB) {
	queries := []string{
		`CREATE TABLE IF NOT EXISTS assets (
			id INTEGER PRIMARY KEY AUTOINCREMENT,
			symbol TEXT UNIQUE NOT NULL
		);`,
		`CREATE TABLE IF NOT EXISTS transactions (
			id INTEGER PRIMARY KEY AUTOINCREMENT,
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
}

func seedCPI(db *sql.DB) {
	var count int
	_ = db.QueryRow("SELECT COUNT(*) FROM cpi_index").Scan(&count)
	if count > 0 {
		return
	}
	for p, v := range defaultCPIData {
		db.Exec("INSERT INTO cpi_index (period, index_val) VALUES (?, ?)", p, v)
	}
}

// FIFO Computation & Inflation Adjustment
func computePortfolio(db *sql.DB) ([]LotViewModel, PortfolioSummary) {
	// Fetch CPI table
	cpiMap := make(map[string]float64)
	latestCPI := 198.0
	rows, err := db.Query("SELECT period, index_val FROM cpi_index ORDER BY period ASC")
	if err == nil {
		for rows.Next() {
			var p string
			var v float64
			if err := rows.Scan(&p, &v); err == nil {
				cpiMap[p] = v
				latestCPI = v
			}
		}
		rows.Close()
	}

	// Fetch latest prices cleanly without composite subqueries
	priceMap := make(map[string]float64)
	pRows, err := db.Query(`
    SELECT symbol, close_price 
    FROM daily_prices 
    ORDER BY price_date DESC, rowid DESC
`)
	if err == nil {
		for pRows.Next() {
			var sym string
			var p float64
			if err := pRows.Scan(&sym, &p); err == nil {
				// Because it is ordered DESC, the first time we see a symbol is its latest price
				if _, exists := priceMap[sym]; !exists {
					priceMap[sym] = p
				}
			}
		}
		pRows.Close()
	}

	// Fetch all transactions
	tRows, err := db.Query(`
		SELECT t.id, t.asset_id, a.symbol, t.type, t.trade_date, t.quantity, t.price, t.fees, COALESCE(t.notes, '')
		FROM transactions t
		JOIN assets a ON t.asset_id = a.id
		ORDER BY t.trade_date ASC, t.id ASC
	`)
	if err != nil {
		return nil, PortfolioSummary{}
	}
	defer tRows.Close()

	type OpenLot struct {
		TxID      int64
		Symbol    string
		TradeDate time.Time
		Qty       float64
		BuyPrice  float64
		Notes     string
	}

	assetLots := make(map[string][]OpenLot)

	var closedTrades []ClosedPositionViewModel
	var realizedSummary RealizedSummary

	for tRows.Next() {
		var tx Transaction
		var dStr string
		tRows.Scan(&tx.ID, &tx.AssetID, &tx.Symbol, &tx.Type, &dStr, &tx.Quantity, &tx.Price, &tx.Fees, &tx.Notes)
		tx.TradeDate = parseFlexibleDate(dStr)

		if tx.Type == "BUY" {
			assetLots[tx.Symbol] = append(assetLots[tx.Symbol], OpenLot{
				TxID:      tx.ID,
				Symbol:    tx.Symbol,
				TradeDate: tx.TradeDate,
				Qty:       tx.Quantity,
				BuyPrice:  tx.Price,
				Notes:     tx.Notes,
			})
		} else if tx.Type == "SELL" {
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

				// Compute holding period & tax classification (1 year / 365 days threshold)
				holdingDays := int(tx.TradeDate.Sub(lots[i].TradeDate).Hours() / 24)
				taxType := "STCG"
				if holdingDays > 365 {
					taxType = "LTCG"
				}

				// CPI Inflation indexing at the time of sale
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

				// Combine buy and sell notes if present
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

	var results []LotViewModel
	var summary PortfolioSummary

	for sym, lots := range assetLots {
		currentPrice := priceMap[sym]
		for _, lot := range lots {
			if lot.Qty <= 0 {
				continue
			}

			// If no live price fetched yet, assume buy price
			effectivePrice := currentPrice
			if effectivePrice == 0 {
				effectivePrice = lot.BuyPrice
			}

			// Inflation calculation
			buyPeriod := lot.TradeDate.Format("2006-01")
			buyCPI := cpiMap[buyPeriod]
			if buyCPI == 0 {
				buyCPI = latestCPI
			}

			inflationFactor := 1.0
			if buyCPI > 0 && latestCPI > 0 {
				inflationFactor = latestCPI / buyCPI
			}

			invested := lot.Qty * lot.BuyPrice
			currentVal := lot.Qty * effectivePrice
			nominalPnL := currentVal - invested
			realCostBasis := invested * inflationFactor
			realPnL := currentVal - realCostBasis

			summary.TotalInvested += invested
			summary.CurrentValue += currentVal
			summary.NominalPnL += nominalPnL
			summary.RealPnL += realPnL

			results = append(results, LotViewModel{
				TxID:         lot.TxID,
				Symbol:       lot.Symbol,
				TradeDate:    lot.TradeDate.Format("02 Jan 2006"),
				RemainingQty: lot.Qty,
				BuyPrice:     lot.BuyPrice,
				CurrentPrice: effectivePrice,
				NominalPnL:   nominalPnL,
				RealPnL:      realPnL,
				Notes:        lot.Notes,
			})
		}
	}

	sort.Slice(results, func(i, j int) bool {
		return results[i].Symbol < results[j].Symbol
	})

	return results, summary
}

// Zerodha Kite CSV Parser
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

	count := 0
	for {
		rec, err := reader.Read()
		if err == io.EOF {
			break
		}
		if err != nil {
			return count, err
		}

		rawSym := strings.TrimSpace(rec[colMap["symbol"]])
		tradeType := strings.ToUpper(strings.TrimSpace(rec[colMap["trade_type"]]))
		rawDate := strings.TrimSpace(rec[colMap["trade_date"]])
		qty, _ := strconv.ParseFloat(strings.TrimSpace(rec[colMap["quantity"]]), 64)
		price, _ := strconv.ParseFloat(strings.TrimSpace(rec[colMap["price"]]), 64)

		exchange := "NSE"
		if idx, ok := colMap["exchange"]; ok && idx < len(rec) {
			if ex := strings.ToUpper(strings.TrimSpace(rec[idx])); ex != "" {
				exchange = ex
			}
		}

		qualifiedSymbol := rawSym + ".NS"
		if exchange == "BSE" {
			qualifiedSymbol = rawSym + ".BO"
		}

		parsedDate, err := time.Parse("2006-01-02", rawDate)
		if err != nil {
			parsedDate, _ = time.Parse("02-01-2006", rawDate)
		}
		tradeDate := parsedDate.Format("2006-01-02")

		var assetID int64
		err = tx.QueryRow("SELECT id FROM assets WHERE symbol = ?", qualifiedSymbol).Scan(&assetID)
		if err == sql.ErrNoRows {
			res, _ := tx.Exec("INSERT INTO assets (symbol) VALUES (?)", qualifiedSymbol)
			assetID, _ = res.LastInsertId()
		}

		tx.Exec(`INSERT INTO transactions (asset_id, type, trade_date, quantity, price, notes)
		         VALUES (?, ?, ?, ?, ?, 'Imported from Kite')`, assetID, tradeType, tradeDate, qty, price)
		count++
	}

	return count, tx.Commit()
}

// Background Price Fetchers (Yahoo Finance)
func updateAllPrices(db *sql.DB) {
	rows, err := db.Query("SELECT DISTINCT symbol FROM assets")
	if err != nil {
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

	//var sym string
	//ifz err := rows.Scan(&sym); err == nil {
	for _, sym := range symbols {
		//updatePriceForSymbol(db, sym)
		//price, err := fetchGoogleFinancePrice(sym)
		price, err := fetchYahooV8(sym)
		if err != nil {
			log.Print("unable to get price for %s. error is %s", sym, err.Error())
			continue // go to next item
		}
		fmt.Printf("for %s stock price is %f", sym, price)
		if price > 0 {
			_, err := db.Exec(`INSERT INTO daily_prices (symbol, price_date, close_price) 
			         VALUES (?, date('now'), ?)
			         ON CONFLICT(symbol, price_date) DO UPDATE SET close_price=excluded.close_price`, sym, price)
			if err != nil {
				log.Printf("[DB SAVE ERROR] %s: %v", sym, err)
			} else {
				log.Printf("[PRICE UPDATED] %s -> ₹%.2f", sym, price)
			}
		}
	}

}

func fetchYahooV8(symbol string) (float64, error) {
	url := fmt.Sprintf("https://query2.finance.yahoo.com/v8/finance/chart/%s?interval=1d&range=1d", symbol)

	client := &http.Client{Timeout: 7 * time.Second}
	req, err := http.NewRequest("GET", url, nil)
	if err != nil {
		return 0, err
	}

	req.Header.Set("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36")
	req.Header.Set("Accept", "application/json")

	resp, err := client.Do(req)
	if err != nil {
		return 0, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return 0, fmt.Errorf("status %d", resp.StatusCode)
	}

	var payload struct {
		Chart struct {
			Result []struct {
				Meta struct {
					RegularMarketPrice float64 `json:"regularMarketPrice"`
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
		p := payload.Chart.Result[0].Meta.RegularMarketPrice
		if p > 0 {
			return p, nil
		}
	}

	return 0, fmt.Errorf("price missing in Yahoo payload")
}
func fetchGrowwPrice(symbol string) (float64, error) {
	// Strip .NS or .BO for Groww (e.g., RELIANCE.NS -> RELIANCE)
	cleanSymbol := strings.ToUpper(strings.TrimSuffix(strings.TrimSuffix(symbol, ".NS"), ".BO"))

	exchange := "NSE"
	if strings.HasSuffix(symbol, ".BO") {
		exchange = "BSE"
	}

	url := fmt.Sprintf("https://groww.in/v1/api/stocks_data/v1/tr_live_prices/exchange/%s/segment/CASH/%s/latest", exchange, cleanSymbol)

	client := &http.Client{Timeout: 7 * time.Second}
	req, err := http.NewRequest("GET", url, nil)
	if err != nil {
		return 0, err
	}

	req.Header.Set("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36")
	req.Header.Set("Accept", "application/json")

	resp, err := client.Do(req)
	if err != nil {
		return 0, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return 0, fmt.Errorf("groww returned status %d", resp.StatusCode)
	}

	var data struct {
		Ltp   float64 `json:"ltp"`   // Last Traded Price
		Close float64 `json:"close"` // Previous Close
	}

	if err := json.NewDecoder(resp.Body).Decode(&data); err != nil {
		return 0, err
	}

	if data.Ltp > 0 {
		return data.Ltp, nil
	}
	if data.Close > 0 {
		return data.Close, nil
	}

	return 0, fmt.Errorf("no valid price found on Groww")
}

// Scrapes Google Finance as a secondary fallback
// fetchGoogleFinancePrice extracts the real-time or closing price from Google Finance.
func fetchGoogleFinancePrice(symbol string) (float64, error) {
	// Normalize symbol to Google Finance format (e.g., RELIANCE:NSE or TCS:BOM)
	cleanSymbol := symbol
	exchange := "NSE"

	if strings.HasSuffix(symbol, ".NS") {
		cleanSymbol = strings.TrimSuffix(symbol, ".NS")
		exchange = "NSE"
	} else if strings.HasSuffix(symbol, ".BO") {
		cleanSymbol = strings.TrimSuffix(symbol, ".BO")
		exchange = "BOM"
	}

	url := fmt.Sprintf("https://www.google.com/finance/quote/%s:%s", cleanSymbol, exchange)

	client := &http.Client{Timeout: 8 * time.Second}
	req, err := http.NewRequest("GET", url, nil)
	if err != nil {
		return 0, err
	}

	// Google Finance requires standard browser headers
	req.Header.Set("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")
	req.Header.Set("Accept-Language", "en-US,en;q=0.9")
	req.Header.Set("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8")

	resp, err := client.Do(req)
	if err != nil {
		return 0, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return 0, fmt.Errorf("google finance returned HTTP status %d for %s", resp.StatusCode, symbol)
	}

	bodyBytes, err := io.ReadAll(resp.Body)
	if err != nil {
		return 0, err
	}
	html := string(bodyBytes)

	// Pattern 1: Main Google Finance price container (<div class="YMlKec fxKbKc">...</div>)
	// Example: <div class="YMlKec fxKbKc">₹2,450.75</div> or <div class="YMlKec fxKbKc">2,450.75</div>
	p1 := regexp.MustCompile(`class="YMlKec fxKbKc"[^>]*>([^<]+)</div>`)
	matches := p1.FindStringSubmatch(html)

	var rawPrice string
	if len(matches) > 1 {
		rawPrice = matches[1]
	} else {
		// Pattern 2: Schema.org itemprop="price" meta tag fallback
		p2 := regexp.MustCompile(`<meta\s+itemprop="price"\s+content="([\d\.]+)"`)
		m2 := p2.FindStringSubmatch(html)
		if len(m2) > 1 {
			rawPrice = m2[1]
		}
	}

	if rawPrice == "" {
		return 0, fmt.Errorf("price element not found in HTML for %s:%s", cleanSymbol, exchange)
	}

	// Sanitize output: remove currency symbols (₹, Rs), commas, and spaces
	cleanPrice := strings.NewReplacer("₹", "", "Rs.", "", "Rs", "", ",", "", " ", "").Replace(rawPrice)

	price, err := strconv.ParseFloat(cleanPrice, 64)
	if err != nil {
		return 0, fmt.Errorf("failed to parse '%s' as float: %w", cleanPrice, err)
	}

	return price, nil
}

func updatePriceForSymbol(db *sql.DB, symbol string) {
	url := fmt.Sprintf("https://query1.finance.yahoo.com/v7/finance/quote?symbols=%s", symbol)
	client := &http.Client{Timeout: 8 * time.Second}
	req, _ := http.NewRequest("GET", url, nil)
	req.Header.Set("User-Agent", "Mozilla/5.0")

	resp, err := client.Do(req)
	if err != nil {
		return
	}
	defer resp.Body.Close()

	var data struct {
		QuoteResponse struct {
			Result []struct {
				RegularMarketPrice float64 `json:"regularMarketPrice"`
			} `json:"result"`
		} `json:"quoteResponse"`
	}

	if err := json.NewDecoder(resp.Body).Decode(&data); err == nil && len(data.QuoteResponse.Result) > 0 {
		price := data.QuoteResponse.Result[0].RegularMarketPrice
		if price > 0 {
			db.Exec(`INSERT INTO daily_prices (symbol, price_date, close_price) 
			         VALUES (?, date('now'), ?)
			         ON CONFLICT(symbol, price_date) DO UPDATE SET close_price=excluded.close_price`, symbol, price)
		}
	}
}

// Helper to parse any date format SQLite or inputs might produce
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

	// If the string starts with YYYY-MM-DD (e.g. "2026-04-12 ..."), grab just the first 10 chars
	if len(raw) >= 10 {
		if t, err := time.Parse("2006-01-02", raw[:10]); err == nil {
			return t
		}
	}

	return time.Now()
}
