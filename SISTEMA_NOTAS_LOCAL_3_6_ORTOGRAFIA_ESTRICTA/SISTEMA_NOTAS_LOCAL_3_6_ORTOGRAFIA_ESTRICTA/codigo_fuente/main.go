package main

import (
	"archive/zip"
	"embed"
	"encoding/json"
	"errors"
	"fmt"
	"html"
	"io"
	"io/fs"
	"log"
	"mime"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"os/user"
	"path/filepath"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
	"unicode"
)

const (
	appFamily      = "sistema-notas-local"
	appVersion     = "3.6.0-ortografia-estricta"
	appID          = appFamily + "-" + appVersion
	bindHost       = "0.0.0.0"
	loopbackHost   = "127.0.0.1"
	firstPort      = 8765
	lastPort       = 8795
	maxBodyBytes   = 30 << 20
	maxPhotos      = 30
	statusNew      = "NUEVO"
	statusOpen     = "ABIERTO"
	statusUsed     = "USADO"
	statusClosed   = "INCIDENTE CERRADO"
	autoCloseAfter = 30 * time.Minute
)

//go:embed web/* web/assets/* closure_codes.json corrections.json orthography_vocab.json
var embeddedFiles embed.FS

type Note struct {
	ID                   int64  `json:"id"`
	Folio                string `json:"folio"`
	FolioManual          string `json:"folioManual"`
	FechaClave           string `json:"fechaClave"`
	Titulo               string `json:"titulo"`
	Corporacion          string `json:"corporacion"`
	Municipio            string `json:"municipio"`
	Operador             string `json:"operador"`
	ContenidoHTML        string `json:"contenidoHtml"`
	WorkflowStatus       string `json:"workflowStatus,omitempty"`
	OpenedAt             string `json:"openedAt,omitempty"`
	UsedAt               string `json:"usedAt,omitempty"`
	ClosedAt             string `json:"closedAt,omitempty"`
	ClosureCode          string `json:"closureCode,omitempty"`
	ClosureName          string `json:"closureName,omitempty"`
	ClosureMethod        string `json:"closureMethod,omitempty"`
	ClosureReason        string `json:"closureReason,omitempty"`
	AutoCloseEligible    bool   `json:"autoCloseEligible,omitempty"`
	OrthographyCorrected bool   `json:"orthographyCorrected,omitempty"`
	CreatedAt            string `json:"createdAt"`
	UpdatedAt            string `json:"updatedAt"`
}

type ClosureCode struct {
	Code             string   `json:"code"`
	Name             string   `json:"name"`
	Definition       string   `json:"definition"`
	SourceName       string   `json:"sourceName,omitempty"`
	SourceDefinition string   `json:"sourceDefinition,omitempty"`
	SourcePage       int      `json:"sourcePage,omitempty"`
	Strong           []string `json:"strong"`
	Concepts         []string `json:"concepts"`
}

type IncidentTipification struct {
	Code     string `json:"code"`
	Name     string `json:"name"`
	Type     string `json:"type"`
	Subtype  string `json:"subtype"`
	Priority string `json:"priority"`
}

type IncidentCatalogFile struct {
	Source string                 `json:"source"`
	Count  int                    `json:"count"`
	Items  []IncidentTipification `json:"items"`
}

type ClosureCandidate struct {
	Code       string   `json:"code"`
	Name       string   `json:"name"`
	Definition string   `json:"definition"`
	Score      float64  `json:"score"`
	Evidence   []string `json:"evidence,omitempty"`
}

type ClosureAnalysis struct {
	Recommended  *ClosureCandidate  `json:"recommended,omitempty"`
	Alternatives []ClosureCandidate `json:"alternatives"`
	Confidence   string             `json:"confidence"`
	Reason       string             `json:"reason"`
}

type CorrectionRule struct {
	Key         string
	Replacement string
	Pattern     *regexp.Regexp
}

type Photo struct {
	ID         int64  `json:"id"`
	NoteID     int64  `json:"noteId"`
	StoredName string `json:"storedName"`
	Name       string `json:"name"`
	Mime       string `json:"mime"`
	Size       int64  `json:"size"`
	CreatedAt  string `json:"createdAt"`
}

type Audit struct {
	ID        int64          `json:"id"`
	Action    string         `json:"action"`
	NoteID    int64          `json:"noteId,omitempty"`
	Folio     string         `json:"folio,omitempty"`
	Details   map[string]any `json:"details,omitempty"`
	CreatedAt string         `json:"createdAt"`
}

type Database struct {
	Version     int64   `json:"version"`
	NextNoteID  int64   `json:"nextNoteId"`
	NextPhotoID int64   `json:"nextPhotoId"`
	NextAuditID int64   `json:"nextAuditId"`
	Notes       []Note  `json:"notes"`
	Photos      []Photo `json:"photos"`
	Audit       []Audit `json:"audit"`
}

type Store struct {
	mu      sync.RWMutex
	path    string
	uploads string
	db      Database
}

type noteSummary struct {
	Note
	PhotoCount   int   `json:"photoCount"`
	CoverPhotoID int64 `json:"coverPhotoId,omitempty"`
}

type fullNote struct {
	Note
	PhotoCount   int           `json:"photoCount"`
	CoverPhotoID int64         `json:"coverPhotoId,omitempty"`
	Photos       []photoPublic `json:"photos"`
}

type photoPublic struct {
	ID        int64  `json:"id"`
	Name      string `json:"name"`
	Mime      string `json:"mime"`
	Size      int64  `json:"size"`
	CreatedAt string `json:"createdAt"`
	URL       string `json:"url"`
}

var allowedTag = regexp.MustCompile(`(?is)<\s*(/?)\s*([a-zA-Z0-9]+)(?:\s[^>]*)?>`)
var dangerousBlock = regexp.MustCompile(`(?is)<(?:script|style|iframe|object|embed)[^>]*>.*?</(?:script|style|iframe|object|embed)\s*>`)
var stripTags = regexp.MustCompile(`(?is)<[^>]+>`)
var nonDigits = regexp.MustCompile(`\D`)
var wordPattern = regexp.MustCompile(`[\p{L}ÁÉÍÓÚÜÑáéíóúüñ]{3,}`)
var htmlLineBreaks = regexp.MustCompile(`(?is)<\s*br\s*/?\s*>|</\s*(?:p|div|li|h[1-6])\s*>`)

var (
	serverPort           int
	serverURLs           []string
	closureCatalog       []ClosureCode
	closureByCode        map[string]ClosureCode
	orthographyRules     []CorrectionRule
	orthographyLexicon   map[string][]string
	orthographyByInitial map[rune][]string
	orthographyByLength  map[int][]string
	orthographyFrequency map[string]int
	incidentCatalog      []IncidentTipification
	serverStartedAt      string
	serverHostName       string
	serverOSUser         string
)

func main() {
	mode := ""
	if len(os.Args) > 1 {
		switch strings.ToLower(strings.TrimSpace(os.Args[1])) {
		case "--servidor", "servidor", "server":
			mode = "server"
		case "--cliente", "cliente", "client":
			mode = "client"
		case "--configurar-cliente", "--config", "config":
			mode = "client-config"
		}
	}

	if mode == "" {
		selected, err := runRoleChooser()
		if err != nil {
			showFatal("No se pudo abrir el selector de modo: " + err.Error())
			return
		}
		mode = selected
	}

	switch mode {
	case "server":
		runServerMode()
	case "client":
		runClientMode(false)
	case "client-config":
		runClientMode(true)
	default:
		showFatal("Modo de ejecución no válido.")
	}
}

func runRoleChooser() (string, error) {
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		return "", err
	}
	port := listener.Addr().(*net.TCPAddr).Port
	choice := make(chan string, 1)
	mux := http.NewServeMux()
	server := &http.Server{Handler: mux, ReadHeaderTimeout: 8 * time.Second}

	mux.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "text/html; charset=utf-8")
		w.Header().Set("Cache-Control", "no-store")
		fmt.Fprint(w, `<!doctype html><html lang="es-MX"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Sistema de Notas</title><style>
		*{box-sizing:border-box}body{margin:0;min-height:100vh;display:grid;place-items:center;background:#dedede;font-family:Segoe UI,Arial,sans-serif;color:#173d59}.card{width:min(850px,calc(100% - 28px));background:#fff;border:2px solid #0d3553;border-radius:20px;padding:28px;box-shadow:0 16px 38px rgba(0,0,0,.17)}h1{margin:0 0 8px;font-size:28px}.sub{margin:0 0 22px;color:#586b79;line-height:1.5}.grid{display:grid;grid-template-columns:1fr 1fr;gap:18px}.option{border:2px solid #0d3553;border-radius:17px;background:#2a66a1;padding:22px;color:#fff;display:flex;flex-direction:column;min-height:245px}.option h2{margin:0 0 10px;color:#ffcc00}.option p{margin:0;line-height:1.5;flex:1}.option button{width:100%;min-height:54px;margin-top:22px;border:2px solid #0d3553;border-radius:11px;background:#154e73;color:#ffcc00;font-size:16px;font-weight:800;cursor:pointer}.option.secondary{background:#eef4f8;color:#173d59}.option.secondary h2{color:#154e73}.small{margin-top:18px;color:#667985;font-size:13px;line-height:1.5}@media(max-width:720px){.grid{grid-template-columns:1fr}.card{padding:20px}h1{font-size:23px}}
		</style></head><body><main class="card"><h1>Sistema de Notas Informativas</h1><p class="sub">Este mismo ejecutable sirve en las dos computadoras. En cada PC selecciona cómo se utilizará.</p><div class="grid"><form class="option" method="post" action="/select"><h2>Computadora principal</h2><p>Inicia el servidor central, guarda la base de datos y las fotografías. Esta computadora debe permanecer encendida mientras se use el sistema.</p><input type="hidden" name="mode" value="server"><button type="submit">INICIAR COMO SERVIDOR</button></form><form class="option secondary" method="post" action="/select"><h2>Segunda computadora</h2><p>Se conecta a la computadora principal. Los registros, cambios, eliminaciones y fotografías se reflejan en ambas pantallas.</p><input type="hidden" name="mode" value="client"><button type="submit">CONECTAR COMO CLIENTE</button></form></div><p class="small"><b>Importante:</b> usa “Servidor” únicamente en la PC que conservará la carpeta <code>datos</code>. En la otra PC usa “Cliente”.</p></main></body></html>`)
	})

	mux.HandleFunc("/select", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Método no permitido", http.StatusMethodNotAllowed)
			return
		}
		if err := r.ParseForm(); err != nil {
			http.Error(w, "No se pudo leer la selección", http.StatusBadRequest)
			return
		}
		mode := strings.TrimSpace(r.FormValue("mode"))
		if mode != "server" && mode != "client" {
			http.Error(w, "Selección no válida", http.StatusBadRequest)
			return
		}
		w.Header().Set("Content-Type", "text/html; charset=utf-8")
		fmt.Fprint(w, `<!doctype html><html lang="es-MX"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Iniciando</title><style>body{font-family:Segoe UI,Arial,sans-serif;background:#dedede;margin:0;min-height:100vh;display:grid;place-items:center;color:#154e73}.box{background:#fff;border:2px solid #0d3553;border-radius:18px;padding:30px;text-align:center;box-shadow:0 14px 32px rgba(0,0,0,.15)}.dot{width:16px;height:16px;margin:18px auto;border-radius:50%;background:#ffcc00;animation:p 1s infinite alternate}@keyframes p{to{transform:scale(1.7);opacity:.45}}</style></head><body><div class="box"><h2>Iniciando el sistema…</h2><div class="dot"></div><p>Esta ventana puede cerrarse cuando se abra la aplicación.</p></div></body></html>`)
		select {
		case choice <- mode:
		default:
		}
	})

	go func() {
		_ = server.Serve(listener)
	}()
	openBrowser(fmt.Sprintf("http://127.0.0.1:%d/", port))
	selected := <-choice
	_ = server.Close()
	return selected, nil
}

func runClientMode(forceConfig bool) {
	root, err := applicationDir()
	if err != nil {
		showFatal(err.Error())
		return
	}
	configPath := filepath.Join(root, "servidor.txt")
	current := readServerConfig(configPath)
	if !forceConfig && current != "" {
		if _, err := checkRemoteServer(current); err == nil {
			openBrowser(strings.TrimRight(current, "/") + "/?vista=dashboard")
			return
		}
	}
	if err := runClientConfigurator(configPath, current); err != nil {
		showFatal(err.Error())
	}
}

func normalizeServerAddress(raw string) (string, error) {
	raw = strings.TrimSpace(raw)
	if raw == "" {
		return "", fmt.Errorf("Escribe el enlace mostrado en la computadora principal")
	}
	if !strings.HasPrefix(raw, "http://") && !strings.HasPrefix(raw, "https://") {
		raw = "http://" + raw
	}
	parsed, err := url.Parse(raw)
	if err != nil || parsed.Hostname() == "" {
		return "", fmt.Errorf("El enlace no es válido")
	}
	if parsed.Port() == "" {
		return "", fmt.Errorf("El enlace debe incluir el puerto, por ejemplo: http://192.168.1.25:8765/")
	}
	parsed.Path = "/"
	parsed.RawQuery = ""
	parsed.Fragment = ""
	return strings.TrimRight(parsed.String(), "/") + "/", nil
}

func checkRemoteServer(base string) (map[string]any, error) {
	status := map[string]any{}
	normalized, err := normalizeServerAddress(base)
	if err != nil {
		return status, err
	}
	client := &http.Client{Timeout: 4 * time.Second}
	resp, err := client.Get(normalized + "api/status")
	if err != nil {
		return status, fmt.Errorf("no se pudo conectar con la computadora principal")
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return status, fmt.Errorf("el servidor respondió con error %d", resp.StatusCode)
	}
	if err := json.NewDecoder(io.LimitReader(resp.Body, 1<<20)).Decode(&status); err != nil {
		return status, fmt.Errorf("la respuesta del servidor no es válida")
	}
	if ok, _ := status["ok"].(bool); !ok {
		return status, fmt.Errorf("el servidor no está disponible")
	}
	if family, _ := status["family"].(string); family != appFamily {
		return status, fmt.Errorf("el enlace no corresponde al Sistema de Notas")
	}
	return status, nil
}

func readServerConfig(path string) string {
	data, err := os.ReadFile(path)
	if err != nil {
		return ""
	}
	value, err := normalizeServerAddress(string(data))
	if err != nil {
		return ""
	}
	return value
}

func runClientConfigurator(configPath, current string) error {
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		return fmt.Errorf("no se pudo abrir el configurador: %w", err)
	}
	port := listener.Addr().(*net.TCPAddr).Port
	mux := http.NewServeMux()
	server := &http.Server{Handler: mux, ReadHeaderTimeout: 8 * time.Second}

	render := func(w http.ResponseWriter, value, errorText string) {
		w.Header().Set("Content-Type", "text/html; charset=utf-8")
		fmt.Fprintf(w, `<!doctype html><html lang="es-MX"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Conectar Sistema de Notas</title><style>
		body{font-family:Segoe UI,Arial,sans-serif;background:#e2e2e2;margin:0;min-height:100vh;display:grid;place-items:center;color:#173d59}.card{width:min(650px,calc(100%% - 30px));background:white;border:2px solid #0d3553;border-radius:18px;padding:26px;box-shadow:0 14px 34px rgba(0,0,0,.16)}h1{margin:0 0 10px}.hint{color:#526573;line-height:1.5}.error{background:#fff0f1;color:#9a2535;border:1px solid #cf7b86;border-radius:10px;padding:10px;margin:14px 0}label{display:block;font-weight:700;margin:18px 0 7px}input{width:100%%;box-sizing:border-box;height:48px;border:2px solid #0d3553;border-radius:10px;padding:0 13px;font-size:16px}button{width:100%%;margin-top:16px;height:50px;border:2px solid #0d3553;border-radius:11px;background:#154e73;color:#ffcc00;font-weight:800;font-size:16px;cursor:pointer}.small{font-size:13px;color:#687985;margin-top:16px}</style></head><body><form class="card" method="post" action="/save"><h1>Conectar la segunda computadora</h1><p class="hint">En la computadora principal abre este mismo ejecutable, selecciona <b>Servidor</b>, pulsa <b>Copiar enlace PC 2</b> y pega aquí el enlace.</p>%s<label>Enlace del servidor central</label><input name="server" value="%s" placeholder="http://192.168.1.25:8765/" autofocus required><button type="submit">GUARDAR Y ABRIR EL SISTEMA</button><p class="small">Ambas computadoras deben estar conectadas a la misma red. La computadora principal debe permanecer encendida.</p></form></body></html>`, clientErrorBox(errorText), html.EscapeString(value))
	}

	mux.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		render(w, current, "")
	})
	mux.HandleFunc("/save", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Método no permitido", http.StatusMethodNotAllowed)
			return
		}
		if err := r.ParseForm(); err != nil {
			render(w, current, "No se pudo leer el enlace.")
			return
		}
		value, err := normalizeServerAddress(r.FormValue("server"))
		if err != nil {
			render(w, r.FormValue("server"), err.Error())
			return
		}
		if _, err := checkRemoteServer(value); err != nil {
			render(w, value, "No se pudo conectar: "+err.Error()+". Verifica que el servidor esté abierto y que el Firewall permita la conexión.")
			return
		}
		if err := os.WriteFile(configPath, []byte(value), 0644); err != nil {
			render(w, value, "No se pudo guardar la configuración: "+err.Error())
			return
		}
		http.Redirect(w, r, value+"?vista=dashboard", http.StatusSeeOther)
		go func() {
			time.Sleep(2 * time.Second)
			_ = server.Close()
		}()
	})

	openBrowser(fmt.Sprintf("http://127.0.0.1:%d/", port))
	err = server.Serve(listener)
	if err == http.ErrServerClosed {
		return nil
	}
	return err
}

func clientErrorBox(message string) string {
	if strings.TrimSpace(message) == "" {
		return ""
	}
	return `<div class="error">` + html.EscapeString(message) + `</div>`
}

func runServerMode() {
	root, err := applicationDir()
	if err != nil {
		showFatal(err.Error())
		return
	}
	dataDir := filepath.Join(root, "datos")
	uploads := filepath.Join(dataDir, "uploads")
	backups := filepath.Join(root, "respaldos")
	_ = os.MkdirAll(uploads, 0755)
	_ = os.MkdirAll(backups, 0755)

	logFile, _ := os.OpenFile(filepath.Join(dataDir, "sistema_notas.log"), os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0644)
	if logFile != nil {
		defer logFile.Close()
		log.SetOutput(logFile)
	}

	// Antes de abrir la base local, cierra cualquier otra instancia de esta familia
	// (incluida la misma versión) que siga ejecutándose en segundo plano. Esto evita
	// que el navegador termine conectado a otro EXE/carpeta y parezca que guardar o
	// eliminar no funciona porque en realidad se está viendo otra base local.
	stopRunningInstances()

	store, err := newStore(filepath.Join(dataDir, "sistema_notas.db.json"), uploads)
	if err != nil {
		showFatal("No se pudo abrir la base local: " + err.Error())
		return
	}

	listener, port, err := findListener()
	if err != nil {
		showFatal(err.Error())
		return
	}
	serverPort = port
	serverURLs = networkAddresses(port)
	recordServerStart(store)
	go autoCloseLoop(store)
	baseURL := fmt.Sprintf("http://%s:%d/?v=%s", loopbackHost, port, url.QueryEscape(appVersion))
	_ = os.WriteFile(filepath.Join(dataDir, "puerto.txt"), []byte(strconv.Itoa(port)), 0644)
	linkText := "ENLACE PARA LA SEGUNDA COMPUTADORA\r\n\r\n"
	if len(serverURLs) == 0 {
		linkText += "No se detectó una dirección de red. Verifica que ambas computadoras estén conectadas a la misma red.\r\n"
	} else {
		for _, address := range serverURLs {
			linkText += address + "\r\n"
		}
	}
	linkText += "\r\nLa computadora servidor debe permanecer encendida y con SistemaNotasServidor.exe abierto.\r\n"
	_ = os.WriteFile(filepath.Join(dataDir, "ENLACE_PARA_PC_2.txt"), []byte(linkText), 0644)

	server := &http.Server{
		Handler:           newHandler(store, backups),
		ReadHeaderTimeout: 10 * time.Second,
		IdleTimeout:       90 * time.Second,
	}

	go func() {
		time.Sleep(650 * time.Millisecond)
		openBrowser(baseURL)
	}()
	log.Printf("Servidor iniciado en %s", baseURL)
	if err := server.Serve(listener); err != nil && !errors.Is(err, http.ErrServerClosed) {
		log.Printf("Servidor detenido con error: %v", err)
	}
}

func applicationDir() (string, error) {
	exe, err := os.Executable()
	if err != nil {
		return "", err
	}
	return filepath.Dir(exe), nil
}

func newStore(path, uploads string) (*Store, error) {
	s := &Store{path: path, uploads: uploads}
	if data, err := os.ReadFile(path); err == nil && len(data) > 0 {
		if err := json.Unmarshal(data, &s.db); err != nil {
			return nil, fmt.Errorf("base dañada: %w", err)
		}
	} else if err != nil && !os.IsNotExist(err) {
		return nil, err
	}
	if s.db.Version == 0 {
		s.db.Version = 1
	}
	if s.db.NextNoteID == 0 {
		s.db.NextNoteID = 1
	}
	if s.db.NextPhotoID == 0 {
		s.db.NextPhotoID = 1
	}
	if s.db.NextAuditID == 0 {
		s.db.NextAuditID = 1
	}
	now := time.Now()
	for i := range s.db.Notes {
		note := &s.db.Notes[i]
		if strings.TrimSpace(note.Operador) == "" {
			note.Operador = "SISTEMA"
		}
		if strings.TrimSpace(note.WorkflowStatus) == "" {
			// Las notas históricas no se cierran de golpe al instalar esta actualización.
			note.WorkflowStatus = statusOpen
			if created, err := time.Parse(time.RFC3339, note.CreatedAt); err == nil && now.Sub(created) >= 0 && now.Sub(created) < autoCloseAfter {
				note.AutoCloseEligible = true
			}
		}
		if note.WorkflowStatus == statusClosed || note.UsedAt != "" {
			note.AutoCloseEligible = false
		}
	}
	if err := s.saveLocked(); err != nil {
		return nil, err
	}
	return s, nil
}

func (s *Store) saveLocked() error {
	data, err := json.MarshalIndent(s.db, "", "  ")
	if err != nil {
		return err
	}
	tmp := s.path + ".tmp"
	if err := os.WriteFile(tmp, data, 0644); err != nil {
		return err
	}
	return os.Rename(tmp, s.path)
}

func (s *Store) addAuditLocked(action string, noteID int64, folio string, details map[string]any) {
	s.db.Audit = append(s.db.Audit, Audit{ID: s.db.NextAuditID, Action: action, NoteID: noteID, Folio: folio, Details: details, CreatedAt: nowISO()})
	s.db.NextAuditID++
	if len(s.db.Audit) > 5000 {
		s.db.Audit = append([]Audit(nil), s.db.Audit[len(s.db.Audit)-5000:]...)
	}
}

func newHandler(store *Store, backupDir string) http.Handler {
	mux := http.NewServeMux()
	mux.HandleFunc("/api/status", func(w http.ResponseWriter, r *http.Request) {
		writeJSON(w, http.StatusOK, map[string]any{
			"ok":              true,
			"app":             appID,
			"family":          appFamily,
			"version":         appVersion,
			"serverPort":      serverPort,
			"serverUrls":      serverURLs,
			"localRequest":    requestIsLocal(r),
			"serverStartedAt": serverStartedAt,
			"serverHostName":  serverHostName,
			"serverOSUser":    serverOSUser,
		})
	})
	mux.HandleFunc("/api/state", func(w http.ResponseWriter, r *http.Request) {
		store.mu.RLock()
		defer store.mu.RUnlock()
		writeJSON(w, http.StatusOK, map[string]any{"ok": true, "version": store.db.Version, "count": len(store.db.Notes)})
	})
	mux.HandleFunc("/api/session", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			methodNotAllowed(w)
			return
		}
		loginDispatcher(w, r, store)
	})
	mux.HandleFunc("/api/audit", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodGet {
			methodNotAllowed(w)
			return
		}
		listAudit(w, r, store)
	})
	mux.HandleFunc("/api/closure-codes", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodGet {
			methodNotAllowed(w)
			return
		}
		writeJSON(w, http.StatusOK, map[string]any{"ok": true, "codes": closureCatalog})
	})
	mux.HandleFunc("/api/closure-analysis", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodGet {
			methodNotAllowed(w)
			return
		}
		analyzeClosureHTTP(w, r, store)
	})
	mux.HandleFunc("/api/workflow", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			methodNotAllowed(w)
			return
		}
		workflowAction(w, r, store)
	})
	mux.HandleFunc("/api/orthography", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			methodNotAllowed(w)
			return
		}
		orthographyHTTP(w, r)
	})
	mux.HandleFunc("/api/notes", func(w http.ResponseWriter, r *http.Request) {
		switch r.Method {
		case http.MethodGet:
			listNotes(w, r, store)
		case http.MethodPost:
			createNote(w, r, store)
		default:
			methodNotAllowed(w)
		}
	})
	mux.HandleFunc("/api/notes/", func(w http.ResponseWriter, r *http.Request) {
		id, ok := parseID(r.URL.Path, "/api/notes/")
		if !ok {
			writeError(w, http.StatusNotFound, "Nota no encontrada.")
			return
		}
		switch r.Method {
		case http.MethodGet:
			getNote(w, store, id)
		case http.MethodPut:
			updateNote(w, r, store, id)
		case http.MethodDelete:
			deleteNote(w, r, store, id)
		default:
			methodNotAllowed(w)
		}
	})
	mux.HandleFunc("/api/photos", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			methodNotAllowed(w)
			return
		}
		addPhoto(w, r, store)
	})
	mux.HandleFunc("/api/photos/", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodDelete {
			methodNotAllowed(w)
			return
		}
		id, ok := parseID(r.URL.Path, "/api/photos/")
		if !ok {
			writeError(w, http.StatusNotFound, "Fotografía no encontrada.")
			return
		}
		deletePhoto(w, r, store, id)
	})
	mux.HandleFunc("/photos/", func(w http.ResponseWriter, r *http.Request) {
		id, ok := parseID(r.URL.Path, "/photos/")
		if !ok {
			http.NotFound(w, r)
			return
		}
		servePhoto(w, r, store, id)
	})
	mux.HandleFunc("/api/backup", func(w http.ResponseWriter, r *http.Request) {
		createBackup(w, store, backupDir)
	})
	mux.HandleFunc("/api/shutdown", func(w http.ResponseWriter, r *http.Request) {
		if !requestIsLocal(r) {
			writeError(w, http.StatusForbidden, "Solo la computadora servidor puede cerrar el sistema central.")
			return
		}
		writeJSON(w, http.StatusOK, map[string]any{"ok": true})
		go func() {
			time.Sleep(250 * time.Millisecond)
			os.Exit(0)
		}()
	})

	staticFS, _ := fs.Sub(embeddedFiles, "web")
	fileServer := http.FileServer(http.FS(staticFS))
	mux.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		if strings.HasPrefix(r.URL.Path, "/api/") || strings.HasPrefix(r.URL.Path, "/photos/") {
			http.NotFound(w, r)
			return
		}
		path := strings.TrimPrefix(r.URL.Path, "/")
		if path == "" {
			path = "index.html"
		}
		if _, err := fs.Stat(staticFS, path); err != nil {
			r2 := r.Clone(r.Context())
			r2.URL.Path = "/"
			fileServer.ServeHTTP(w, r2)
			return
		}
		if strings.HasSuffix(path, ".html") || strings.HasSuffix(path, ".js") || strings.HasSuffix(path, ".css") {
			w.Header().Set("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
			w.Header().Set("Pragma", "no-cache")
			w.Header().Set("Expires", "0")
		}
		fileServer.ServeHTTP(w, r)
	})
	return withRecovery(mux)
}

func listNotes(w http.ResponseWriter, r *http.Request, s *Store) {
	q := strings.ToLower(strings.TrimSpace(r.URL.Query().Get("q")))
	corp := strings.TrimSpace(r.URL.Query().Get("corporation"))
	s.mu.RLock()
	defer s.mu.RUnlock()
	countByNote := map[int64]int{}
	coverByNote := map[int64]int64{}
	for _, p := range s.db.Photos {
		countByNote[p.NoteID]++
		if coverByNote[p.NoteID] == 0 || p.ID < coverByNote[p.NoteID] {
			coverByNote[p.NoteID] = p.ID
		}
	}
	result := make([]noteSummary, 0, len(s.db.Notes))
	for _, n := range s.db.Notes {
		if corp != "" && n.Corporacion != corp {
			continue
		}
		if q != "" {
			haystack := strings.ToLower(n.Folio + " " + n.Titulo + " " + n.Municipio + " " + stripHTML(n.ContenidoHTML))
			if !strings.Contains(haystack, q) {
				continue
			}
		}
		result = append(result, noteSummary{Note: n, PhotoCount: countByNote[n.ID], CoverPhotoID: coverByNote[n.ID]})
	}
	sort.Slice(result, func(i, j int) bool {
		if result[i].FechaClave != result[j].FechaClave {
			return result[i].FechaClave > result[j].FechaClave
		}
		return result[i].ID > result[j].ID
	})
	writeJSON(w, http.StatusOK, map[string]any{"ok": true, "notes": result, "version": s.db.Version})
}

func getNote(w http.ResponseWriter, s *Store, id int64) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	for _, n := range s.db.Notes {
		if n.ID != id {
			continue
		}
		photos := []photoPublic{}
		var cover int64
		for _, p := range s.db.Photos {
			if p.NoteID == id {
				if cover == 0 || p.ID < cover {
					cover = p.ID
				}
				photos = append(photos, photoPublic{ID: p.ID, Name: p.Name, Mime: p.Mime, Size: p.Size, CreatedAt: p.CreatedAt, URL: fmt.Sprintf("/photos/%d", p.ID)})
			}
		}
		sort.Slice(photos, func(i, j int) bool { return photos[i].ID < photos[j].ID })
		writeJSON(w, http.StatusOK, map[string]any{"ok": true, "note": fullNote{Note: n, PhotoCount: len(photos), CoverPhotoID: cover, Photos: photos}, "version": s.db.Version})
		return
	}
	writeError(w, http.StatusNotFound, "La nota no existe.")
}

func createNote(w http.ResponseWriter, r *http.Request, s *Store) {
	operator := dispatcherFromRequest(r)
	if operator == "" {
		writeError(w, http.StatusUnauthorized, "Inicia sesión de despacho antes de registrar una nota.")
		return
	}
	var input Note
	if err := decodeJSON(r, &input); err != nil {
		writeError(w, http.StatusBadRequest, err.Error())
		return
	}
	input.Operador = operator
	validated, err := validateNote(input, "")
	if err != nil {
		writeError(w, http.StatusBadRequest, err.Error())
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	for _, n := range s.db.Notes {
		if n.Folio == validated.Folio {
			writeError(w, http.StatusConflict, "El folio ya existe. Utilice otra terminación.")
			return
		}
	}
	now := nowISO()
	validated.ID = s.db.NextNoteID
	s.db.NextNoteID++
	validated.CreatedAt = now
	validated.UpdatedAt = now
	validated.WorkflowStatus = statusNew
	validated.AutoCloseEligible = true
	s.db.Notes = append(s.db.Notes, validated)
	s.addAuditLocked("CREAR_NOTA", validated.ID, validated.Folio, map[string]any{
		"corporacion": validated.Corporacion,
		"operador":    operator,
		"ip":          clientIP(r),
	})
	s.db.Version++
	if err := s.saveLocked(); err != nil {
		writeError(w, http.StatusInternalServerError, err.Error())
		return
	}
	writeJSON(w, http.StatusCreated, map[string]any{
		"ok": true, "id": validated.ID, "folio": validated.Folio,
		"version": s.db.Version, "orthographyCorrected": validated.OrthographyCorrected,
	})
}

func updateNote(w http.ResponseWriter, r *http.Request, s *Store, id int64) {
	operator := dispatcherFromRequest(r)
	if operator == "" {
		writeError(w, http.StatusUnauthorized, "Inicia sesión de despacho antes de editar una nota.")
		return
	}
	var input Note
	if err := decodeJSON(r, &input); err != nil {
		writeError(w, http.StatusBadRequest, err.Error())
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	index := -1
	for i := range s.db.Notes {
		if s.db.Notes[i].ID == id {
			index = i
			break
		}
	}
	if index < 0 {
		writeError(w, http.StatusNotFound, "La nota no existe.")
		return
	}
	old := s.db.Notes[index]
	input.Operador = old.Operador
	validated, err := validateNote(input, old.FechaClave)
	if err != nil {
		writeError(w, http.StatusBadRequest, err.Error())
		return
	}
	for _, n := range s.db.Notes {
		if n.ID != id && n.Folio == validated.Folio {
			writeError(w, http.StatusConflict, "El folio ya existe. Utilice otra terminación.")
			return
		}
	}
	validated.ID = id
	validated.CreatedAt = old.CreatedAt
	validated.UpdatedAt = nowISO()
	validated.Operador = old.Operador
	validated.WorkflowStatus = old.WorkflowStatus
	validated.OpenedAt = old.OpenedAt
	validated.UsedAt = old.UsedAt
	validated.ClosedAt = old.ClosedAt
	validated.ClosureCode = old.ClosureCode
	validated.ClosureName = old.ClosureName
	validated.ClosureMethod = old.ClosureMethod
	validated.ClosureReason = old.ClosureReason
	validated.AutoCloseEligible = old.AutoCloseEligible
	validated.OrthographyCorrected = validated.OrthographyCorrected || old.OrthographyCorrected
	s.db.Notes[index] = validated
	s.addAuditLocked("EDITAR_NOTA", id, validated.Folio, map[string]any{
		"folioAnterior": old.Folio,
		"operador":      operator,
		"ip":            clientIP(r),
	})
	s.db.Version++
	if err := s.saveLocked(); err != nil {
		writeError(w, http.StatusInternalServerError, err.Error())
		return
	}
	writeJSON(w, http.StatusOK, map[string]any{
		"ok": true, "id": id, "folio": validated.Folio, "version": s.db.Version,
		"orthographyCorrected": validated.OrthographyCorrected,
	})
}

func deleteNote(w http.ResponseWriter, r *http.Request, s *Store, id int64) {
	s.mu.Lock()
	index := -1
	var folio string
	for i, n := range s.db.Notes {
		if n.ID == id {
			index, folio = i, n.Folio
			break
		}
	}
	if index < 0 {
		s.mu.Unlock()
		writeError(w, http.StatusNotFound, "La nota no existe.")
		return
	}
	files := []string{}
	keptPhotos := s.db.Photos[:0]
	for _, p := range s.db.Photos {
		if p.NoteID == id {
			files = append(files, p.StoredName)
		} else {
			keptPhotos = append(keptPhotos, p)
		}
	}
	s.db.Photos = keptPhotos
	s.db.Notes = append(s.db.Notes[:index], s.db.Notes[index+1:]...)
	s.addAuditLocked("ELIMINAR_NOTA", id, folio, map[string]any{"operador": dispatcherOrSystem(r), "ip": clientIP(r)})
	s.db.Version++
	err := s.saveLocked()
	version := s.db.Version
	s.mu.Unlock()
	if err != nil {
		writeError(w, http.StatusInternalServerError, err.Error())
		return
	}
	for _, file := range files {
		_ = os.Remove(filepath.Join(s.uploads, file))
	}
	writeJSON(w, http.StatusOK, map[string]any{"ok": true, "version": version})
}

func addPhoto(w http.ResponseWriter, r *http.Request, s *Store) {
	noteID, err := strconv.ParseInt(r.URL.Query().Get("note_id"), 10, 64)
	if err != nil || noteID <= 0 {
		writeError(w, http.StatusBadRequest, "Identificador de nota inválido.")
		return
	}
	name, _ := url.QueryUnescape(r.URL.Query().Get("name"))
	if name == "" {
		name = "imagen"
	}
	contentType := strings.ToLower(strings.TrimSpace(strings.Split(r.Header.Get("Content-Type"), ";")[0]))
	ext := map[string]string{"image/jpeg": ".jpg", "image/png": ".png", "image/webp": ".webp", "image/gif": ".gif"}[contentType]
	if ext == "" {
		writeError(w, http.StatusBadRequest, "Solo se permiten imágenes JPG, PNG, WEBP o GIF.")
		return
	}
	r.Body = http.MaxBytesReader(w, r.Body, 20<<20)
	data, err := io.ReadAll(r.Body)
	if err != nil || len(data) == 0 {
		writeError(w, http.StatusBadRequest, "La imagen está vacía o supera 20 MB.")
		return
	}

	s.mu.Lock()
	var folio string
	exists := false
	count := 0
	for _, n := range s.db.Notes {
		if n.ID == noteID {
			exists, folio = true, n.Folio
			break
		}
	}
	for _, p := range s.db.Photos {
		if p.NoteID == noteID {
			count++
		}
	}
	if !exists {
		s.mu.Unlock()
		writeError(w, http.StatusNotFound, "La nota no existe.")
		return
	}
	if count >= maxPhotos {
		s.mu.Unlock()
		writeError(w, http.StatusBadRequest, fmt.Sprintf("La nota admite un máximo de %d fotografías.", maxPhotos))
		return
	}
	stored := fmt.Sprintf("%d_%d_%d%s", noteID, time.Now().UnixNano(), s.db.NextPhotoID, ext)
	if err := os.WriteFile(filepath.Join(s.uploads, stored), data, 0644); err != nil {
		s.mu.Unlock()
		writeError(w, http.StatusInternalServerError, err.Error())
		return
	}
	p := Photo{ID: s.db.NextPhotoID, NoteID: noteID, StoredName: stored, Name: truncate(name, 180), Mime: contentType, Size: int64(len(data)), CreatedAt: nowISO()}
	s.db.NextPhotoID++
	s.db.Photos = append(s.db.Photos, p)
	s.addAuditLocked("AGREGAR_FOTO", noteID, folio, map[string]any{"photoId": p.ID, "size": len(data), "operador": dispatcherOrSystem(r), "ip": clientIP(r)})
	s.db.Version++
	err = s.saveLocked()
	version := s.db.Version
	s.mu.Unlock()
	if err != nil {
		_ = os.Remove(filepath.Join(s.uploads, stored))
		writeError(w, http.StatusInternalServerError, err.Error())
		return
	}
	writeJSON(w, http.StatusCreated, map[string]any{"ok": true, "photoId": p.ID, "url": fmt.Sprintf("/photos/%d", p.ID), "version": version})
}

func deletePhoto(w http.ResponseWriter, r *http.Request, s *Store, id int64) {
	s.mu.Lock()
	index := -1
	var photo Photo
	var folio string
	for i, p := range s.db.Photos {
		if p.ID == id {
			index, photo = i, p
			break
		}
	}
	if index < 0 {
		s.mu.Unlock()
		writeError(w, http.StatusNotFound, "La fotografía no existe.")
		return
	}
	for _, n := range s.db.Notes {
		if n.ID == photo.NoteID {
			folio = n.Folio
			break
		}
	}
	s.db.Photos = append(s.db.Photos[:index], s.db.Photos[index+1:]...)
	s.addAuditLocked("ELIMINAR_FOTO", photo.NoteID, folio, map[string]any{"photoId": id, "operador": dispatcherOrSystem(r), "ip": clientIP(r)})
	s.db.Version++
	err := s.saveLocked()
	version := s.db.Version
	s.mu.Unlock()
	if err != nil {
		writeError(w, http.StatusInternalServerError, err.Error())
		return
	}
	_ = os.Remove(filepath.Join(s.uploads, photo.StoredName))
	writeJSON(w, http.StatusOK, map[string]any{"ok": true, "version": version})
}

func servePhoto(w http.ResponseWriter, r *http.Request, s *Store, id int64) {
	s.mu.RLock()
	var photo *Photo
	for i := range s.db.Photos {
		if s.db.Photos[i].ID == id {
			copy := s.db.Photos[i]
			photo = &copy
			break
		}
	}
	s.mu.RUnlock()
	if photo == nil {
		http.NotFound(w, r)
		return
	}
	path := filepath.Join(s.uploads, photo.StoredName)
	w.Header().Set("Content-Type", photo.Mime)
	w.Header().Set("Cache-Control", "public, max-age=31536000, immutable")
	w.Header().Set("Content-Disposition", "inline; filename=\""+safeHeaderFilename(photo.Name)+"\"")
	http.ServeFile(w, r, path)
}

func createBackup(w http.ResponseWriter, s *Store, backupDir string) {
	stamp := time.Now().Format("20060102_150405")
	name := "respaldo_notas_" + stamp + ".zip"
	path := filepath.Join(backupDir, name)
	file, err := os.Create(path)
	if err != nil {
		writeError(w, http.StatusInternalServerError, err.Error())
		return
	}
	zw := zip.NewWriter(file)
	s.mu.RLock()
	dbData, _ := json.MarshalIndent(s.db, "", "  ")
	photos := append([]Photo(nil), s.db.Photos...)
	s.mu.RUnlock()
	entry, _ := zw.Create("datos/sistema_notas.db.json")
	_, _ = entry.Write(dbData)
	for _, p := range photos {
		data, err := os.ReadFile(filepath.Join(s.uploads, p.StoredName))
		if err != nil {
			continue
		}
		entry, _ := zw.Create("datos/uploads/" + p.StoredName)
		_, _ = entry.Write(data)
	}
	entry, _ = zw.Create("LEEME.txt")
	_, _ = entry.Write([]byte("Respaldo del Sistema de Notas Informativas.\r\nCreado: " + nowISO() + "\r\n"))
	_ = zw.Close()
	_ = file.Close()
	w.Header().Set("Content-Type", "application/zip")
	w.Header().Set("Content-Disposition", `attachment; filename="`+name+`"`)
	info, statErr := os.Stat(path)
	if statErr != nil {
		writeError(w, http.StatusInternalServerError, statErr.Error())
		return
	}
	w.Header().Set("Content-Length", strconv.FormatInt(info.Size(), 10))
	f, openErr := os.Open(path)
	if openErr != nil {
		writeError(w, http.StatusInternalServerError, openErr.Error())
		return
	}
	defer f.Close()
	_, _ = io.Copy(w, f)
}

func validateNote(input Note, existingDate string) (Note, error) {
	manual := normalizeManual(input.FolioManual)
	dateKey := nonDigits.ReplaceAllString(input.FechaClave, "")
	if existingDate != "" {
		dateKey = existingDate
	}
	originalTitle := strings.TrimSpace(input.Titulo)
	input.Titulo = truncate(correctPlainText(originalTitle), 160)
	input.Corporacion = truncate(strings.TrimSpace(input.Corporacion), 20)
	input.Municipio = truncate(strings.TrimSpace(input.Municipio), 100)
	input.Operador = truncate(strings.TrimSpace(input.Operador), 100)
	if input.Operador == "" {
		input.Operador = "SISTEMA"
	}
	originalHTML := sanitizeHTML(input.ContenidoHTML)
	input.ContenidoHTML = normalizeNoteStructureHTML(correctHTMLOrthography(originalHTML))
	input.OrthographyCorrected = input.Titulo != originalTitle || input.ContenidoHTML != originalHTML
	if len(dateKey) != 8 {
		return Note{}, errors.New("La fecha de la nota no es válida.")
	}
	if manual == "" || strings.Trim(manual, "0") == "" {
		return Note{}, errors.New("Escriba la terminación del folio.")
	}
	if input.Titulo == "" {
		return Note{}, errors.New("Escriba el título del incidente.")
	}
	if input.Corporacion == "" {
		return Note{}, errors.New("Seleccione una corporación.")
	}
	if input.Municipio == "" {
		return Note{}, errors.New("Escriba el municipio.")
	}
	if len(strings.TrimSpace(stripHTML(input.ContenidoHTML))) < 5 {
		return Note{}, errors.New("Escriba el contenido de la nota informativa.")
	}
	input.FolioManual = manual
	input.FechaClave = dateKey
	input.Folio = "REF/" + dateKey + "/" + manual
	return input, nil
}

func sanitizeHTML(value string) string {
	value = dangerousBlock.ReplaceAllString(value, "")
	allowed := map[string]bool{"p": true, "br": true, "b": true, "strong": true, "i": true, "em": true, "u": true, "ul": true, "ol": true, "li": true, "div": true}
	return strings.TrimSpace(allowedTag.ReplaceAllStringFunc(value, func(tagText string) string {
		m := allowedTag.FindStringSubmatch(tagText)
		if len(m) < 3 {
			return ""
		}
		tag := strings.ToLower(m[2])
		if !allowed[tag] {
			return ""
		}
		if tag == "br" {
			return "<br>"
		}
		if m[1] == "/" {
			return "</" + tag + ">"
		}
		return "<" + tag + ">"
	}))
}

func stripHTML(value string) string {
	return strings.Join(strings.Fields(html.UnescapeString(stripTags.ReplaceAllString(value, " "))), " ")
}

func normalizeManual(value string) string {
	digits := nonDigits.ReplaceAllString(value, "")
	if len(digits) > 20 {
		digits = digits[:20]
	}
	return digits
}

func parseID(path, prefix string) (int64, bool) {
	value := strings.TrimPrefix(path, prefix)
	if value == path || strings.Contains(value, "/") {
		return 0, false
	}
	id, err := strconv.ParseInt(value, 10, 64)
	return id, err == nil && id > 0
}

func decodeJSON(r *http.Request, target any) error {
	r.Body = http.MaxBytesReader(nil, r.Body, 2<<20)
	dec := json.NewDecoder(r.Body)
	if err := dec.Decode(target); err != nil {
		return errors.New("Los datos enviados no son válidos.")
	}
	return nil
}

func writeJSON(w http.ResponseWriter, status int, value any) {
	w.Header().Set("Content-Type", "application/json; charset=utf-8")
	w.Header().Set("Cache-Control", "no-store")
	w.WriteHeader(status)
	_ = json.NewEncoder(w).Encode(value)
}

func writeError(w http.ResponseWriter, status int, message string) {
	writeJSON(w, status, map[string]any{"ok": false, "error": message})
}

func methodNotAllowed(w http.ResponseWriter) {
	writeError(w, http.StatusMethodNotAllowed, "Método no permitido.")
}

func nowISO() string { return time.Now().Format(time.RFC3339) }

func truncate(value string, max int) string {
	r := []rune(value)
	if len(r) > max {
		return string(r[:max])
	}
	return value
}

func safeHeaderFilename(value string) string {
	value = strings.ReplaceAll(value, "\r", "")
	value = strings.ReplaceAll(value, "\n", "")
	value = strings.ReplaceAll(value, "\"", "'")
	value = strings.TrimSpace(value)
	if value == "" {
		return "imagen"
	}
	return truncate(value, 160)
}

func clientIP(r *http.Request) string {
	if r == nil {
		return ""
	}
	host, _, err := net.SplitHostPort(r.RemoteAddr)
	if err == nil {
		return strings.Trim(host, "[]")
	}
	return strings.Trim(r.RemoteAddr, "[]")
}

func dispatcherFromRequest(r *http.Request) string {
	if r == nil {
		return ""
	}
	value := strings.TrimSpace(r.Header.Get("X-Dispatcher"))
	value = strings.Join(strings.Fields(value), " ")
	return truncate(value, 80)
}

func dispatcherOrSystem(r *http.Request) string {
	if value := dispatcherFromRequest(r); value != "" {
		return value
	}
	return "SISTEMA"
}

func loginDispatcher(w http.ResponseWriter, r *http.Request, s *Store) {
	var payload struct {
		Name string `json:"name"`
	}
	if err := decodeJSON(r, &payload); err != nil {
		writeError(w, http.StatusBadRequest, err.Error())
		return
	}
	name := strings.ToUpper(strings.Join(strings.Fields(strings.TrimSpace(payload.Name)), " "))
	name = truncate(name, 80)
	if len([]rune(name)) < 2 {
		writeError(w, http.StatusBadRequest, "Escribe el nombre o clave del despachador.")
		return
	}
	s.mu.Lock()
	s.addAuditLocked("INICIAR_SESION", 0, "", map[string]any{
		"operador":  name,
		"ip":        clientIP(r),
		"navegador": truncate(r.UserAgent(), 180),
	})
	s.db.Version++
	err := s.saveLocked()
	version := s.db.Version
	s.mu.Unlock()
	if err != nil {
		writeError(w, http.StatusInternalServerError, err.Error())
		return
	}
	writeJSON(w, http.StatusOK, map[string]any{"ok": true, "name": name, "version": version})
}

func listAudit(w http.ResponseWriter, r *http.Request, s *Store) {
	limit := 80
	if raw := strings.TrimSpace(r.URL.Query().Get("limit")); raw != "" {
		if value, err := strconv.Atoi(raw); err == nil && value > 0 {
			if value > 300 {
				value = 300
			}
			limit = value
		}
	}
	s.mu.RLock()
	start := len(s.db.Audit) - limit
	if start < 0 {
		start = 0
	}
	items := append([]Audit(nil), s.db.Audit[start:]...)
	s.mu.RUnlock()
	for i, j := 0, len(items)-1; i < j; i, j = i+1, j-1 {
		items[i], items[j] = items[j], items[i]
	}
	writeJSON(w, http.StatusOK, map[string]any{
		"ok":              true,
		"audit":           items,
		"serverStartedAt": serverStartedAt,
		"serverHostName":  serverHostName,
		"serverOSUser":    serverOSUser,
	})
}

func recordServerStart(s *Store) {
	serverStartedAt = nowISO()
	serverHostName, _ = os.Hostname()
	serverOSUser = strings.TrimSpace(os.Getenv("USERNAME"))
	if serverOSUser == "" {
		serverOSUser = strings.TrimSpace(os.Getenv("USER"))
	}
	if current, err := user.Current(); err == nil && strings.TrimSpace(current.Username) != "" {
		serverOSUser = current.Username
	}
	if serverOSUser == "" {
		serverOSUser = "USUARIO DESCONOCIDO"
	}
	if serverHostName == "" {
		serverHostName = "PC DESCONOCIDA"
	}
	s.mu.Lock()
	s.addAuditLocked("INICIAR_SERVIDOR", 0, "", map[string]any{
		"usuarioSO": serverOSUser,
		"pc":        serverHostName,
		"puerto":    serverPort,
		"version":   appVersion,
	})
	s.db.Version++
	_ = s.saveLocked()
	s.mu.Unlock()
}

func orthographyHTTP(w http.ResponseWriter, r *http.Request) {
	var payload struct {
		Title string `json:"title"`
		HTML  string `json:"html"`
		Text  string `json:"text"`
	}
	if err := decodeJSON(r, &payload); err != nil {
		writeError(w, http.StatusBadRequest, err.Error())
		return
	}
	correctedTitle := correctPlainText(payload.Title)
	correctedHTML := normalizeNoteStructureHTML(correctHTMLOrthography(payload.HTML))
	correctedText := correctPlainText(payload.Text)
	writeJSON(w, http.StatusOK, map[string]any{
		"ok":      true,
		"title":   correctedTitle,
		"html":    correctedHTML,
		"text":    correctedText,
		"changed": correctedTitle != payload.Title || correctedHTML != payload.HTML || correctedText != payload.Text,
	})
}

func loadEmbeddedCatalogs() {
	closureCatalog = []ClosureCode{}
	closureByCode = map[string]ClosureCode{}
	if data, err := embeddedFiles.ReadFile("closure_codes.json"); err == nil {
		_ = json.Unmarshal(data, &closureCatalog)
	}
	for _, item := range closureCatalog {
		closureByCode[item.Code] = item
	}

	incidentCatalog = []IncidentTipification{}
	if data, err := embeddedFiles.ReadFile("web/tipificaciones.json"); err == nil {
		var catalog IncidentCatalogFile
		if json.Unmarshal(data, &catalog) == nil {
			incidentCatalog = catalog.Items
		}
	}

	corrections := map[string]string{}
	if data, err := embeddedFiles.ReadFile("corrections.json"); err == nil {
		_ = json.Unmarshal(data, &corrections)
	}
	keys := make([]string, 0, len(corrections))
	for key := range corrections {
		key = strings.TrimSpace(key)
		if key != "" {
			keys = append(keys, key)
		}
	}
	sort.Slice(keys, func(i, j int) bool {
		return len([]rune(keys[i])) > len([]rune(keys[j]))
	})
	orthographyRules = orthographyRules[:0]
	for _, key := range keys {
		replacement := strings.TrimSpace(corrections[key])
		if replacement == "" {
			continue
		}
		pattern := regexp.MustCompile(`(?i)(^|[^\p{L}])(` + regexp.QuoteMeta(key) + `)([^\p{L}]|$)`)
		orthographyRules = append(orthographyRules, CorrectionRule{Key: key, Replacement: replacement, Pattern: pattern})
	}

	vocab := map[string]int{}
	if data, err := embeddedFiles.ReadFile("orthography_vocab.json"); err == nil {
		_ = json.Unmarshal(data, &vocab)
	}
	buildOrthographyLexicon(corrections, vocab)
}

func orthographyKey(value string) string {
	return strings.ToLower(normalizeClosureText(value))
}

func addLexiconWordFreq(word string, freq int) {
	word = strings.TrimSpace(strings.ToLower(word))
	if len([]rune(word)) < 3 {
		return
	}
	key := orthographyKey(word)
	if key == "" || strings.Contains(key, " ") {
		return
	}
	values := orthographyLexicon[key]
	for _, existing := range values {
		if existing == word {
			if freq > 0 {
				orthographyFrequency[key] += freq
			}
			return
		}
	}
	orthographyLexicon[key] = append(values, word)
	if freq <= 0 {
		freq = 1
	}
	orthographyFrequency[key] += freq
}

func addLexiconWord(word string) { addLexiconWordFreq(word, 1) }

func addLexiconText(text string) {
	for _, word := range wordPattern.FindAllString(text, -1) {
		addLexiconWordFreq(word, 2)
	}
}

func buildOrthographyLexicon(corrections map[string]string, vocab map[string]int) {
	orthographyLexicon = map[string][]string{}
	orthographyByInitial = map[rune][]string{}
	orthographyByLength = map[int][]string{}
	orthographyFrequency = map[string]int{}
	for word, freq := range vocab {
		addLexiconWordFreq(word, freq)
	}
	for _, replacement := range corrections {
		addLexiconText(replacement)
	}
	for _, item := range incidentCatalog {
		addLexiconText(item.Name)
		addLexiconText(item.Type)
		addLexiconText(item.Subtype)
	}
	for _, item := range closureCatalog {
		addLexiconText(item.Name)
		addLexiconText(item.Definition)
	}
	// Vocabulario operativo frecuente que aparece en notas informativas. Todo queda local/offline.
	addLexiconText(`arribo arribar arribaron acudió acudieron atención atendió atendida atendido valorar valoró valoración signos vitales estabilización estabilizó primeros auxilios prehospitalaria paramédico paramédica ambulancia traslado trasladó trasladada trasladado hospital clínica institución salud paciente persona masculino femenino aproximadamente posteriormente inmediatamente domicilio dirección colonia municipio localidad referencia unidad móvil motopatrulla patrulla elemento elementos comandante supervisor operador despacho reporte reportante responsable afectada afectado lesionada lesionado lesiones inconsciente consciente emergencia incidente hechos lugar sitio apoyo solicitud solicitó informó manifestó indicó verificó localizó encontró desconocido desconocida fuego incendio llamas humo bodega vivienda comercio pastizal basura controlado sofocado extinguido fuga derrame combustible gasolina vehículo motocicleta automóvil conductor conductores tránsito vialidad accidente percance aseguradora aseguradoras convenio acuerdo particulares daños corralón infracción fiscalía ministerio público disposición detenido detenida flagrancia persecución orientación información canalización instancia competente prevención preventivo vigilancia rondín seguridad protección civil policía municipal estatal bomberos rescate rescatada rescatado evacuación evacuada evacuado acordonamiento perímetro riesgo población ciudadanía institución hospitalaria falleció fallecida fallecido deceso occisa occiso semefo albergue refugio negativa negó tratamiento asesoría telefónica alarma bancaria banco seproban grabación aplicativo monitoreo seguimiento consigna inteligencia investigación localización desaparecida localizado localizada`)
	// Palabras españolas válidas y frecuentes que se protegen para evitar falsas correcciones.
	addLexiconText(`media medio medios hora horas minuto minutos antes después durante cada general generales parte partes estado estados base bases calle calles avenida avenidas zona zonas ejido ranchería carretera camino punto puntos personal servicio servicios salida entradas entrada regreso tiempo día días noche mañana tarde momento momentos forma manera área áreas domicilio domicilios casa casas lugar lugares sitio sitios nombre nombres datos dato cargo cargos tipo tipos jefe jefa turno turnos apoyo apoyos reporte reportes ciudadano ciudadana ciudadanos ciudadanas vehículo vehículos unidad unidades móvil móviles radio radios orden órdenes daños material materiales particular particulares público pública públicos públicas`)
	for key := range orthographyLexicon {
		runes := []rune(key)
		if len(runes) == 0 {
			continue
		}
		orthographyByInitial[runes[0]] = append(orthographyByInitial[runes[0]], key)
		orthographyByLength[len(runes)] = append(orthographyByLength[len(runes)], key)
	}
}

func damerauDistance(a, b string) int {
	ra := []rune(a)
	rb := []rune(b)
	if len(ra) == 0 {
		return len(rb)
	}
	if len(rb) == 0 {
		return len(ra)
	}
	d := make([][]int, len(ra)+1)
	for i := range d {
		d[i] = make([]int, len(rb)+1)
		d[i][0] = i
	}
	for j := range d[0] {
		d[0][j] = j
	}
	for i := 1; i <= len(ra); i++ {
		for j := 1; j <= len(rb); j++ {
			cost := 0
			if ra[i-1] != rb[j-1] {
				cost = 1
			}
			v := d[i-1][j] + 1
			if x := d[i][j-1] + 1; x < v {
				v = x
			}
			if x := d[i-1][j-1] + cost; x < v {
				v = x
			}
			if i > 1 && j > 1 && ra[i-1] == rb[j-2] && ra[i-2] == rb[j-1] {
				if x := d[i-2][j-2] + 1; x < v {
					v = x
				}
			}
			d[i][j] = v
		}
	}
	return d[len(ra)][len(rb)]
}

func sameLetters(value string) string {
	runes := []rune(value)
	sort.Slice(runes, func(i, j int) bool { return runes[i] < runes[j] })
	return string(runes)
}

func safeTypoShape(input, candidate string) bool {
	if input == candidate {
		return false
	}
	a := []rune(input)
	b := []rune(candidate)
	diff := absInt(len(a) - len(b))
	if diff > 2 {
		return false
	}
	if diff <= 1 {
		return true
	}
	// Dos letras de diferencia sólo se aceptan en palabras suficientemente largas.
	return len(a) >= 7 && len(b) >= 7
}

func absInt(v int) int {
	if v < 0 {
		return -v
	}
	return v
}

func maxTypoDistance(length int) int {
	if length <= 5 {
		return 1
	}
	if length <= 7 {
		return 1
	}
	return 2
}

func fuzzyCorrectWord(original string) string {
	key := orthographyKey(original)
	if key == "" || strings.Contains(key, " ") || len([]rune(key)) < 3 {
		return original
	}
	if variants := orthographyLexicon[key]; len(variants) == 1 {
		canonical := variants[0]
		if strings.EqualFold(original, canonical) {
			return original
		}
		return applyCaseStyle(original, canonical)
	} else if len(variants) > 1 {
		return original
	}

	letters := []rune(original)
	if len(letters) > 1 && unicode.IsUpper(letters[0]) {
		allUpper := true
		for _, r := range letters[1:] {
			if unicode.IsLetter(r) && !unicode.IsUpper(r) {
				allUpper = false
				break
			}
		}
		if !allUpper {
			return original
		} // proteger nombres propios
	}

	kr := []rune(key)
	maxDist := maxTypoDistance(len(kr))
	candidateSet := map[string]struct{}{}
	if len(kr) > 0 {
		for _, c := range orthographyByInitial[kr[0]] {
			candidateSet[c] = struct{}{}
		}
	}
	// Para palabras de 6+ letras también considerar primera letra equivocada/omitida.
	if len(kr) >= 6 {
		for l := len(kr) - maxDist; l <= len(kr)+maxDist; l++ {
			for _, c := range orthographyByLength[l] {
				candidateSet[c] = struct{}{}
			}
		}
	}
	type scored struct {
		key  string
		dist int
		freq int
	}
	best := scored{dist: 99}
	second := scored{dist: 99}
	for candidateKey := range candidateSet {
		if !safeTypoShape(key, candidateKey) {
			continue
		}
		dist := damerauDistance(key, candidateKey)
		if dist > maxDist {
			continue
		}
		freq := orthographyFrequency[candidateKey]
		cur := scored{candidateKey, dist, freq}
		better := func(a, b scored) bool {
			if a.dist != b.dist {
				return a.dist < b.dist
			}
			return a.freq > b.freq
		}
		if better(cur, best) {
			second = best
			best = cur
		} else if better(cur, second) {
			second = cur
		}
	}
	if best.key == "" || best.dist > maxDist {
		return original
	}
	// En distancia 2 exigimos una ventaja real para evitar cambiar palabras válidas.
	if best.dist == 2 {
		if second.key != "" && second.dist == best.dist && best.freq < second.freq*3 {
			return original
		}
		if best.freq < 2 {
			return original
		}
	} else if second.key != "" && second.dist == best.dist && best.freq == second.freq {
		return original
	}
	variants := orthographyLexicon[best.key]
	if len(variants) != 1 {
		return original
	}
	return applyCaseStyle(original, variants[0])
}

func applyCaseStyle(original, replacement string) string {
	letters := []rune(original)
	allUpper := true
	allLower := true
	seenLetter := false
	for _, r := range letters {
		if !unicode.IsLetter(r) {
			continue
		}
		seenLetter = true
		if unicode.IsLower(r) {
			allUpper = false
		}
		if unicode.IsUpper(r) {
			allLower = false
		}
	}
	if seenLetter && allUpper {
		return strings.ToUpper(replacement)
	}
	if seenLetter && allLower {
		return strings.ToLower(replacement)
	}
	if len(letters) > 0 && unicode.IsUpper(letters[0]) {
		runes := []rune(strings.ToLower(replacement))
		if len(runes) > 0 {
			runes[0] = unicode.ToUpper(runes[0])
		}
		return string(runes)
	}
	return replacement
}

func correctPlainText(value string) string {
	result := value
	for _, rule := range orthographyRules {
		result = rule.Pattern.ReplaceAllStringFunc(result, func(match string) string {
			parts := rule.Pattern.FindStringSubmatch(match)
			if len(parts) != 4 {
				return match
			}
			return parts[1] + applyCaseStyle(parts[2], rule.Replacement) + parts[3]
		})
	}
	// Segunda capa: restaura acentos inequívocos y corrige transposiciones/letras duplicadas
	// usando el vocabulario local ampliado del CNIE, códigos de cierre y español operativo.
	result = wordPattern.ReplaceAllStringFunc(result, fuzzyCorrectWord)
	// Tercera capa: vuelve a aplicar reglas de frase. Esto corrige casos encadenados,
	// por ejemplo ATENCIO MEDIA -> ATENCIÓN MEDIA -> ATENCIÓN MÉDICA.
	for _, rule := range orthographyRules {
		result = rule.Pattern.ReplaceAllStringFunc(result, func(match string) string {
			parts := rule.Pattern.FindStringSubmatch(match)
			if len(parts) != 4 {
				return match
			}
			return parts[1] + applyCaseStyle(parts[2], rule.Replacement) + parts[3]
		})
	}
	return result
}

func correctHTMLOrthography(value string) string {
	if strings.TrimSpace(value) == "" {
		return value
	}
	var out strings.Builder
	start := 0
	for _, loc := range stripTags.FindAllStringIndex(value, -1) {
		if loc[0] > start {
			out.WriteString(correctPlainText(value[start:loc[0]]))
		}
		out.WriteString(value[loc[0]:loc[1]])
		start = loc[1]
	}
	if start < len(value) {
		out.WriteString(correctPlainText(value[start:]))
	}
	return out.String()
}

func normalizeNoteStructureHTML(value string) string {
	if strings.TrimSpace(value) == "" {
		return value
	}
	// Normalización visual segura para notas pegadas desde WhatsApp u otros sistemas.
	// No cambia el orden ni el significado: solo unifica bloques y marcadores *texto*.
	value = regexp.MustCompile(`(?is)<\s*div\s*>`).ReplaceAllString(value, "<p>")
	value = regexp.MustCompile(`(?is)</\s*div\s*>`).ReplaceAllString(value, "</p>")
	whatsappBold := regexp.MustCompile(`\*([^*<>\n]{1,220})\*`)
	value = whatsappBold.ReplaceAllString(value, "<strong>$1</strong>")
	// Evita huecos excesivos que dificultan identificar el resultado final del incidente.
	excessBreaks := regexp.MustCompile(`(?is)(?:<\s*br\s*/?\s*>\s*){4,}`)
	value = excessBreaks.ReplaceAllString(value, "<br><br>")
	emptyParas := regexp.MustCompile(`(?is)<p>\s*(?:&nbsp;|<br\s*/?>|\s)*</p>`)
	value = emptyParas.ReplaceAllString(value, "")
	return strings.TrimSpace(value)
}

func plainNoteLines(value string) []string {
	value = htmlLineBreaks.ReplaceAllString(value, "\n")
	value = stripTags.ReplaceAllString(value, "")
	value = html.UnescapeString(value)
	value = strings.ReplaceAll(value, "\r", "\n")
	parts := strings.Split(value, "\n")
	lines := make([]string, 0, len(parts))
	for _, line := range parts {
		line = strings.TrimSpace(line)
		line = strings.Trim(line, "*#•- \t")
		line = strings.TrimSpace(line)
		if line != "" {
			lines = append(lines, line)
		}
	}
	return lines
}

func isMetadataClosureLine(normalized string) bool {
	prefixes := []string{
		"SECRETARIA ", "SECRETARIA MUNICIPAL", "FECHA ", "FECHA:", "HORA ", "HORA:",
		"SOLICITA ", "SOLICITA:", "AMBULANCIA ", "AMBULANCIA:", "JEFE DE SERVICIO", "TIPO DE SERVICIO",
		"CRONOMETRIA", "AVISO ", "AVISO:", "LLEGADA AL LUGAR", "SALIDA DE BASE", "SALIDA DEL LUGAR",
		"REGRESO A BASE", "UNIDAD ", "UNIDAD:", "FOLIO ", "FOLIO:", "MUNICIPIO ", "MUNICIPIO:",
	}
	for _, prefix := range prefixes {
		if strings.HasPrefix(normalized, prefix) {
			return true
		}
	}
	return false
}

func isOutcomeMarker(normalized string) bool {
	markers := []string{"RESULTADO", "CIERRE", "CONCLUSION", "OBSERVACIONES", "ACCIONES REALIZADAS", "ATENCION BRINDADA", "SITUACION FINAL", "NOVEDADES"}
	for _, marker := range markers {
		if normalized == marker || strings.HasPrefix(normalized, marker+" ") {
			return true
		}
	}
	return false
}

func hasOutcomeVerb(normalized string) bool {
	needles := []string{
		"ATEND", "VALOR", "TRASLAD", "FALLEC", "SIN SIGNOS VITALES", "NEG", "RECHAZ", "RESCAT", "EVACU",
		"DETEN", "DISPOSICION", "FUGA", "REMIT", "CORRALON", "INFRACCION", "CONVENIO", "ACUERDO", "ASEGURAD",
		"CONTROL", "SOFOC", "EXTING", "LOCALIZ", "NO SE LOCALIZ", "NO SE HIZO CONTACTO", "ORIENT", "CANALIZ",
		"INFORMA A LA CORPORACION", "NOTIFICO A LA CORPORACION", "ACORDON", "INTELIGENCIA", "SIMULACRO", "CONSIGNA",
		"MONITOREO", "SEPROBAN", "ALARMA", "COMBUSTIBLE", "FALTA DE UNIDADES", "ORDEN SUPERIOR", "SEMEFO", "ALBERGUE",
	}
	for _, needle := range needles {
		if strings.Contains(normalized, needle) {
			return true
		}
	}
	return false
}

func uniqueAppend(list []string, seen map[string]bool, value string) []string {
	key := normalizeClosureText(value)
	if key == "" || seen[key] {
		return list
	}
	seen[key] = true
	return append(list, value)
}

func closureTextSections(note Note) (full string, tail string, outcome string) {
	lines := plainNoteLines(note.ContenidoHTML)
	narrative := make([]string, 0, len(lines))
	outcomeLines := []string{}
	seenOutcome := map[string]bool{}
	inOutcome := false
	for _, line := range lines {
		n := normalizeClosureText(line)
		if n == "" {
			continue
		}
		if isOutcomeMarker(n) {
			inOutcome = true
			// No descartamos la misma línea: muchas notas escriben
			// "RESULTADO FINAL: ..." y el resultado viene a continuación del marcador.
		}
		if isMetadataClosureLine(n) {
			continue
		}
		narrative = append(narrative, line)
		if inOutcome || hasOutcomeVerb(n) {
			outcomeLines = uniqueAppend(outcomeLines, seenOutcome, line)
		}
	}
	// Las definiciones del catálogo de cierre se basan en las últimas notas: siempre ponderar
	// también las últimas líneas narrativas aunque no traigan una etiqueta formal de resultado.
	start := len(narrative) - 7
	if start < 0 {
		start = 0
	}
	for _, line := range narrative[start:] {
		outcomeLines = uniqueAppend(outcomeLines, seenOutcome, line)
	}
	full = normalizeClosureText(strings.Join(narrative, " "))
	tail = tailRunes(full, 3400)
	outcome = normalizeClosureText(strings.Join(outcomeLines, " "))
	outcome = tailRunes(outcome, 2200)
	if outcome == "" {
		outcome = tailRunes(tail, 1400)
	}
	return full, tail, outcome
}

func directStrongClosure(outcome, tail string) (string, string) {
	bestCode := ""
	bestPhrase := ""
	bestWeight := 0
	commonSingles := map[string]bool{"APOYO": true, "FUGA": true, "RESCATE": true, "CONVENIO": true, "EVACUACION": true, "TRASLADO": true, "ATENCION": true, "UNIDAD": true, "ALARMA": true}
	for _, item := range closureCatalog {
		for _, phrase := range item.Strong {
			needle := normalizeClosureText(phrase)
			if needle == "" {
				continue
			}
			words := len(strings.Fields(needle))
			if words == 1 && commonSingles[needle] {
				continue
			}
			weight := len([]rune(needle)) + words*12
			matched := strings.Contains(outcome, needle)
			if !matched && words >= 2 {
				matched = strings.Contains(tail, needle)
				weight -= 12
			}
			if matched && weight > bestWeight {
				bestWeight = weight
				bestCode = item.Code
				bestPhrase = phrase
			}
		}
	}
	if bestCode != "" && bestWeight >= 28 {
		return bestCode, "COINCIDENCIA DIRECTA EN EL RESULTADO DE LA NOTA: " + bestPhrase
	}
	return "", ""
}

func closureTokenSet(value string) map[string]bool {
	stop := map[string]bool{
		"ACUERDO": true, "NOTAS": true, "NOTA": true, "INCIDENTE": true, "EMPLEA": true, "CUANDO": true, "LUGAR": true,
		"EMERGENCIA": true, "REPORTAN": true, "REPORTANTE": true, "PARTE": true, "PERSONA": true, "UNIDAD": true, "CORPORACION": true,
		"REALIZA": true, "REALIZAN": true, "AFECTADA": true, "AFECTADO": true, "POSTERIOR": true, "GENERALMENTE": true, "ACUDE": true,
		"LLEGA": true, "MISMO": true, "MISMA": true, "ALGUNA": true, "ALGUN": true, "SOBRE": true, "ENTRE": true, "TODAS": true,
	}
	set := map[string]bool{}
	for _, token := range strings.Fields(normalizeClosureText(value)) {
		if len([]rune(token)) < 5 || stop[token] {
			continue
		}
		set[token] = true
	}
	return set
}

func normalizeClosureText(value string) string {
	value = html.UnescapeString(value)
	value = strings.ToUpper(value)
	replacer := strings.NewReplacer(
		"Á", "A", "É", "E", "Í", "I", "Ó", "O", "Ú", "U", "Ü", "U", "Ñ", "N",
		"À", "A", "È", "E", "Ì", "I", "Ò", "O", "Ù", "U", "Ç", "C",
	)
	value = replacer.Replace(value)
	var out strings.Builder
	lastSpace := true
	for _, r := range value {
		if unicode.IsLetter(r) || unicode.IsDigit(r) {
			out.WriteRune(r)
			lastSpace = false
		} else if !lastSpace {
			out.WriteByte(' ')
			lastSpace = true
		}
	}
	return strings.TrimSpace(out.String())
}

func tailRunes(value string, max int) string {
	runes := []rune(value)
	if len(runes) <= max {
		return value
	}
	return string(runes[len(runes)-max:])
}

func containsAnyNormalized(text string, phrases ...string) bool {
	for _, phrase := range phrases {
		needle := normalizeClosureText(phrase)
		if needle != "" && strings.Contains(text, needle) {
			return true
		}
	}
	return false
}

func decisiveClosure(last, tail, full string) (string, string) {
	// Primero se resuelven resultados irreversibles y combinaciones específicas.
	// Así, por ejemplo, una muerte durante un traslado nunca queda clasificada como simple traslado.
	if containsAnyNormalized(tail, "TRASLADO A INSTITUCION DE SALUD Y MUERTO EN SITIO", "TRASLADADA A UNA INSTITUCION DE SALUD Y POSTERIOR MUERE EN EL LUGAR", "TRASLADADO A UNA INSTITUCION DE SALUD Y POSTERIOR MUERE EN EL LUGAR") {
		return "37", "LA NARRATIVA INDICA TRASLADO A UNA INSTITUCIÓN DE SALUD Y POSTERIOR MUERTE EN SITIO"
	}
	if containsAnyNormalized(tail, "FALLECIO EN EL HOSPITAL", "PERDIO LA VIDA EN EL HOSPITAL", "MUERTO EN INSTITUCION DE SALUD", "FALLECIO DENTRO DE LA INSTITUCION DE SALUD", "FALLECE DENTRO DE LA INSTITUCION DE SALUD") {
		return "48", "LA PERSONA FALLECIÓ EN UNA INSTITUCIÓN DE SALUD"
	}
	if containsAnyNormalized(tail, "FALLECIO DURANTE EL TRASLADO", "PERDIO LA VIDA DURANTE EL TRASLADO", "MUERTO EN TRASLADO", "REALIZA EL TRASLADO Y LA PARTE AFECTADA FALLECE") ||
		(containsAnyNormalized(tail, "DURANTE EL TRASLADO", "EN TRASLADO") && containsAnyNormalized(tail, "FALLECIO", "PERDIO LA VIDA", "DECESO")) {
		return "47", "LA PERSONA FALLECIÓ DURANTE EL TRASLADO"
	}
	if containsAnyNormalized(tail, "DELINCUENTE MUERTO EN PERSECUCION", "RESPONSABLE FALLECIO DURANTE LA PERSECUCION") || (strings.Contains(tail, "FUGA") && containsAnyNormalized(tail, "RESPONSABLE FALLECE", "RESPONSABLE FALLECIO")) {
		return "16", "EL RESPONSABLE FALLECIÓ DURANTE LA PERSECUCIÓN"
	}
	if containsAnyNormalized(tail, "SIN SIGNOS VITALES", "FALLECIO EN EL LUGAR", "MUERTO EN SITIO", "MUERE EN EL LUGAR DE LA EMERGENCIA", "PERSONA AFECTADA MUERE EN EL LUGAR") {
		return "19", "LA PERSONA FUE LOCALIZADA SIN SIGNOS VITALES EN EL SITIO"
	}

	// Reglas médicas prioritarias para diferenciar atención en sitio, traslado y ambas acciones.
	noTransfer := containsAnyNormalized(tail, "NO REQUIRIO TRASLADO", "NO AMERITO TRASLADO", "NO FUE TRASLADADO", "NO FUE TRASLADADA")
	transfer := !noTransfer && containsAnyNormalized(tail, "TRASLADADO", "TRASLADADA", "TRASLADO", "SE TRASLADA", "FUE TRASLADADO", "FUE TRASLADADA")
	hospital := containsAnyNormalized(tail, "HOSPITAL", "INSTITUCION DE SALUD", "CLINICA", "URGENCIAS", "HGR", "IMSS", "CENTRO DE SALUD")
	directMedical := containsAnyNormalized(tail,
		"VALORADO EN EL LUGAR", "VALORADA EN EL LUGAR", "SE VALORO EN EL LUGAR", "VALORACION EN EL SITIO",
		"ATENDIDO EN EL LUGAR", "ATENDIDA EN EL LUGAR", "ATENCION EN SITIO", "ATENCION EN EL SITIO",
		"ATENCION MEDICA EN SITIO", "ATENCION MEDICA EN EL SITIO", "ATENCION PREHOSPITALARIA EN EL SITIO",
		"ATENCION PREHOSPITALARIA EN EL LUGAR", "PRIMEROS AUXILIOS EN EL SITIO", "PRIMEROS AUXILIOS EN EL LUGAR",
		"FUE ESTABILIZADO EN EL LUGAR", "FUE ESTABILIZADA EN EL LUGAR", "SE LE BRINDO ATENCION PREHOSPITALARIA",
		"UNIDAD MEDICA ATIENDE O VALORA", "ATIENDE O VALORA A LA PARTE AFECTADA EN EL LUGAR", "VALORA A LA PARTE AFECTADA EN EL LUGAR")
	clinical := containsAnyNormalized(tail, "VALORACION PRIMARIA", "VALORACION PREHOSPITALARIA", "TOMA DE SIGNOS VITALES", "SIGNOS VITALES", "INMOVILIZACION", "CONTROL DE HEMORRAGIA", "CURACION", "VENDAJE", "ESTABILIZACION", "OXIGENO")
	arrival := containsAnyNormalized(tail, "AL ARRIBAR", "AL LLEGAR", "EN EL LUGAR", "EN EL SITIO")
	medicalSite := directMedical || (arrival && clinical)
	if containsAnyNormalized(tail, "SE NEGO A LA ATENCION", "SE NIEGA A SER VALORADA", "SE NIEGA A SER VALORADO", "SE NIEGA A SER ATENDIDA", "SE NIEGA A SER ATENDIDO", "RECHAZO LA ATENCION", "FIRMO NEGATIVA", "NO ACEPTO SER VALORADO", "NO ACEPTO SER VALORADA") {
		return "25", "LA PERSONA SE NEGÓ A SER VALORADA O ATENDIDA"
	}
	if containsAnyNormalized(tail, "TRASLADADO A UN ALBERGUE", "TRASLADADA A UN ALBERGUE", "TRASLADO AL ALBERGUE", "CANALIZADO A REFUGIO") {
		return "26", "LA PERSONA FUE TRASLADADA A UN ALBERGUE O REFUGIO"
	}
	if containsAnyNormalized(tail, "TRASLADO A SEMEFO", "TRASLADADO AL SEMEFO", "TRASLADADA AL SEMEFO", "SERVICIO MEDICO FORENSE") {
		return "27", "LA PERSONA OCCISA FUE TRASLADADA AL SEMEFO"
	}
	if containsAnyNormalized(tail, "TRASLADADO POR SUS PROPIOS MEDIOS", "TRASLADADA POR SUS PROPIOS MEDIOS", "TRASLADARA A LA PARTE AFECTADA POR SUS PROPIOS MEDIOS", "TRASLADARA POR SUS PROPIOS MEDIOS", "FAMILIARES LO TRASLADARON", "FAMILIARES LA TRASLADARON", "VEHICULO PARTICULAR") {
		return "34", "EL TRASLADO FUE REALIZADO POR UN PARTICULAR O POR SUS PROPIOS MEDIOS"
	}
	if medicalSite && transfer && hospital {
		return "35", "LA NARRATIVA CONFIRMA ATENCIÓN O VALORACIÓN EN SITIO Y POSTERIOR TRASLADO A UNA INSTITUCIÓN DE SALUD"
	}
	if transfer && hospital {
		return "46", "LA NARRATIVA CONFIRMA TRASLADO A UNA INSTITUCIÓN DE SALUD SIN EVIDENCIA SUFICIENTE DE ATENCIÓN EN SITIO"
	}
	if medicalSite && !transfer {
		return "17", "LA PERSONA FUE ATENDIDA O VALORADA EN EL SITIO SIN TRASLADO"
	}
	if containsAnyNormalized(tail, "ATENDIDO EN EL HOSPITAL", "ATENDIDA EN EL HOSPITAL", "RECIBIO ATENCION EN EL HOSPITAL", "ATENDIDO EN UNA INSTITUCION DE SALUD", "ATENDIDA EN UNA INSTITUCION DE SALUD") && !transfer {
		return "18", "LA PERSONA RECIBIÓ ATENCIÓN MÉDICA EN UNA INSTITUCIÓN DE SALUD"
	}
	if containsAnyNormalized(tail, "ASESORIA MEDICA", "PRIMEROS AUXILIOS VIA TELEFONICA", "INDICACIONES MEDICAS POR TELEFONO", "ASISTENCIA TELEFONICA") {
		return "44", "SE BRINDÓ ASESORÍA MÉDICA O PRIMEROS AUXILIOS POR VÍA TELEFÓNICA"
	}

	// Reglas combinadas de seguridad y tránsito que prevalecen sobre coincidencias simples.
	if containsAnyNormalized(tail, "PERSONA FUGADA Y VEHICULO REMITIDO", "RESPONSABLE SE DIO A LA FUGA Y EL VEHICULO FUE REMITIDO") {
		return "54", "EL RESPONSABLE HUYÓ Y EL VEHÍCULO FUE REMITIDO"
	}
	if containsAnyNormalized(tail, "PERSONA DETENIDA Y VEHICULO REMITIDO", "DETENIDO Y VEHICULO AL CORRALON", "DETENCION DEL CONDUCTOR Y REMISION DEL VEHICULO") {
		return "55", "HUBO DETENCIÓN Y REMISIÓN DEL VEHÍCULO"
	}
	if containsAnyNormalized(tail, "DETENIDO EN FUGA", "DETENIDO CUANDO SE DABA A LA FUGA") {
		if containsAnyNormalized(tail, "MINISTERIO PUBLICO", "DISPOSICION DEL M.P") {
			return "74", "LA PERSONA FUE DETENIDA EN FUGA Y PUESTA A DISPOSICIÓN DEL M.P."
		}
		if containsAnyNormalized(tail, "POLICIA MUNICIPAL", "DISPOSICION DE LA P.M") {
			return "49", "LA PERSONA FUE DETENIDA EN FUGA Y PUESTA A DISPOSICIÓN DE LA P.M."
		}
	}
	if containsAnyNormalized(tail, "DETENIDO EN FLAGRANCIA", "DETENCION EN FLAGRANCIA", "DETENIDO EN EL LUGAR") {
		if containsAnyNormalized(tail, "MINISTERIO PUBLICO", "DISPOSICION DEL M.P") {
			return "5", "LA PERSONA FUE DETENIDA EN FLAGRANCIA Y PUESTA A DISPOSICIÓN DEL M.P."
		}
		if containsAnyNormalized(tail, "POLICIA MUNICIPAL", "DISPOSICION DE LA P.M") {
			return "23", "LA PERSONA FUE DETENIDA EN FLAGRANCIA Y PUESTA A DISPOSICIÓN DE LA P.M."
		}
	}
	if containsAnyNormalized(tail, "ARREGLO ENTRE PARTICULARES", "NO INTERVINO TRANSITO", "LLEGARON A UN ARREGLO POR SU CUENTA") {
		return "58", "LAS PARTES LLEGARON A UN ARREGLO SIN INTERVENCIÓN DEL AGENTE DE TRÁNSITO"
	}
	if containsAnyNormalized(tail, "ASEGURADORAS SE RESPONSABILIZAN", "SE HICIERON CARGO LAS ASEGURADORAS", "AJUSTADORES SE HICIERON CARGO") {
		return "59", "LAS ASEGURADORAS SE RESPONSABILIZARON DE LOS DAÑOS"
	}
	if containsAnyNormalized(tail, "CADA CONDUCTOR SE RESPONSABILIZO DE SUS DANOS", "CADA PARTE SE HIZO RESPONSABLE DE SUS DANOS") {
		return "57", "LOS CONDUCTORES SE RESPONSABILIZARON DE SUS DAÑOS"
	}
	if containsAnyNormalized(tail, "SEPROBAN") {
		if containsAnyNormalized(tail, "APLICATIVO") {
			return "68", "LA ALERTA DE SEPROBAN FUE RECIBIDA MEDIANTE APLICATIVO"
		}
		if containsAnyNormalized(tail, "GRABACION", "MENSAJE GRABADO") {
			return "66", "LA ALERTA DE SEPROBAN FUE RECIBIDA MEDIANTE GRABACIÓN"
		}
		if containsAnyNormalized(tail, "LLAMADA", "OPERADOR") {
			return "67", "LA ALERTA DE SEPROBAN FUE RECIBIDA MEDIANTE LLAMADA"
		}
	}
	if containsAnyNormalized(tail, "ALARMA", "CENTRAL DE ALARMAS") && containsAnyNormalized(tail, "BANCO", "BANCARIA") {
		if containsAnyNormalized(tail, "GRABACION", "GRABADORA", "CONMUTADOR", "MENSAJE GRABADO") {
			return "65", "LA ALERTA BANCARIA FUE RECIBIDA MEDIANTE GRABACIÓN O CONMUTADOR"
		}
		if containsAnyNormalized(tail, "LLAMADA", "OPERADOR TELEFONICO") {
			return "64", "LA ALERTA BANCARIA FUE RECIBIDA MEDIANTE LLAMADA"
		}
	}

	if containsAnyNormalized(tail, "VEHICULO RECUPERADO", "SE ENCONTRO SU VEHICULO EN OTRO LUGAR", "REPORTANTE MANIFIESTE QUE SE ENCONTRO SU VEHICULO") {
		return "41", "EL VEHÍCULO REPORTADO FUE RECUPERADO"
	}
	if strings.Contains(tail, "FUGA") && containsAnyNormalized(tail, "VEHICULO ES REMITIDO", "VEHICULO FUE REMITIDO", "VEHICULO REMITIDO", "CORRALON", "FISCALIA") {
		return "54", "EL RESPONSABLE HUYÓ Y EL VEHÍCULO FUE REMITIDO"
	}
	if containsAnyNormalized(tail, "DETENCION DEL RESPONSABLE EN EL MOMENTO DE LA FUGA", "DETENCION DEL RESPONSABLE EN MOMENTO DE LA FUGA") && containsAnyNormalized(tail, "DISPOSICION DEL M.P", "MINISTERIO PUBLICO") {
		return "74", "LA PERSONA FUE DETENIDA EN FUGA Y PUESTA A DISPOSICIÓN DEL M.P."
	}

	// Resultados operativos frecuentes.
	if containsAnyNormalized(tail, "SOLICITO CANCELAR EL APOYO", "YA NO REQUIERE EL APOYO", "REPORTANTE CANCELO") {
		return "32", "EL REPORTANTE CANCELÓ EXPRESAMENTE EL APOYO"
	}
	if containsAnyNormalized(tail, "FALTA DE UNIDADES", "NO HAY UNIDADES DISPONIBLES") {
		return "36", "EL INCIDENTE NO FUE ATENDIDO POR FALTA DE UNIDADES"
	}
	if containsAnyNormalized(tail, "FALTA DE COMBUSTIBLE", "SIN GASOLINA") {
		return "71", "LA UNIDAD NO ACUDIÓ POR FALTA DE COMBUSTIBLE"
	}
	if containsAnyNormalized(tail, "UNIDADES CONCENTRADAS", "POR ORDEN SUPERIOR", "POR INSTRUCCIONES SUPERIORES") {
		return "73", "LAS UNIDADES ESTABAN CONCENTRADAS POR ORDEN SUPERIOR"
	}
	if containsAnyNormalized(tail, "QUEMA DE BASURA", "BASURA QUEMANDOSE") {
		return "77", "EL FUEGO REPORTADO CORRESPONDIÓ A QUEMA DE BASURA"
	}
	if strings.Contains(tail, "PASTIZAL") && containsAnyNormalized(tail, "CONTROLADO", "SOFOCADO", "EXTINGUIDO") {
		return "76", "EL INCENDIO DE PASTIZAL QUEDÓ CONTROLADO"
	}
	if containsAnyNormalized(tail, "CONTROLADO POR EL PROPIETARIO", "SOFOCADO POR EL PROPIETARIO", "VECINOS CONTROLARON") {
		return "75", "EL INCENDIO FUE CONTROLADO POR EL PROPIETARIO O VECINOS"
	}
	if containsAnyNormalized(tail, "SE EXTINGUIO EL INCENDIO", "INCENDIO SOFOCADO", "SE SOFOCARON LAS LLAMAS", "FUEGO EXTINGUIDO", "ERRADICA EL FUEGO") {
		return "21", "LA CORPORACIÓN EXTINGUIÓ EL FUEGO"
	}
	if containsAnyNormalized(tail, "DIRECCION INCORRECTA", "DOMICILIO NO EXISTE", "NO SE LOCALIZO EL DOMICILIO") {
		return "8", "EL DOMICILIO REPORTADO ES INCORRECTO O NO EXISTE"
	}
	if containsAnyNormalized(tail, "NO SE LOCALIZO AL REPORTANTE", "REPORTANTE NO SALIO", "NO FUE POSIBLE CONTACTAR AL REPORTANTE") {
		return "43", "NO SE LOGRÓ CONTACTO CON EL INCIDENTE O REPORTANTE"
	}
	if containsAnyNormalized(tail, "NO SE LOCALIZO A LA PERSONA OFENDIDA", "AGRAVIADO NO LOCALIZADO") {
		return "69", "LA UNIDAD NO LOCALIZÓ A LA PERSONA OFENDIDA"
	}
	if containsAnyNormalized(tail, "NO ENCONTRO INDICIO DELICTIVO", "SIN INDICIOS DELICTIVOS", "NO SE CORROBORO EL HECHO DELICTIVO") {
		return "70", "LA UNIDAD VERIFICÓ Y NO ENCONTRÓ INDICIOS DELICTIVOS"
	}
	if containsAnyNormalized(tail, "NO HAY INDICIOS", "TODO SE ENCONTRO SIN NOVEDAD") && !strings.Contains(tail, "DELICT") {
		return "2", "NO SE ENCONTRARON INDICIOS DE LA EMERGENCIA REPORTADA"
	}
	if containsAnyNormalized(tail, "SE REALIZO EL RESCATE", "PERSONA RESCATADA", "ANIMAL RESCATADO") {
		return "30", "LA CORPORACIÓN REALIZÓ UN RESCATE"
	}
	if containsAnyNormalized(tail, "PERSONA LOCALIZADA", "YA FUE LOCALIZADA", "FUE ENCONTRADA CON VIDA") {
		return "60", "LA PERSONA REPORTADA FUE LOCALIZADA"
	}
	if containsAnyNormalized(tail, "ACORDONAMIENTO PREVENTIVO", "SE ACORDONO EL AREA", "PERIMETRO DE SEGURIDAD") {
		return "78", "SE REALIZÓ ACORDONAMIENTO PREVENTIVO"
	}
	if containsAnyNormalized(tail, "LABOR DE INTELIGENCIA", "TRABAJOS DE INTELIGENCIA") {
		return "79", "SE REALIZARON LABORES DE INTELIGENCIA"
	}
	if containsAnyNormalized(tail, "APOYO PREVENTIVO", "RECORRIDOS PREVENTIVOS", "PRESENCIA PREVENTIVA", "VIGILANCIA PREVENTIVA") {
		return "7", "SE PROPORCIONÓ APOYO PREVENTIVO"
	}

	_ = last
	_ = full
	return "", ""
}

func closureContextAdjustment(code string, tail string) float64 {
	noTransfer := containsAnyNormalized(tail, "NO REQUIRIO TRASLADO", "NO AMERITO TRASLADO", "NO FUE TRASLADADO", "NO FUE TRASLADADA")
	hasTransfer := !noTransfer && containsAnyNormalized(tail, "TRASLADADO", "TRASLADADA", "TRASLADO", "SE TRASLADA")
	hasHospital := containsAnyNormalized(tail, "HOSPITAL", "INSTITUCION DE SALUD", "CLINICA", "URGENCIAS", "HGR", "IMSS")
	hasMedicalSite := containsAnyNormalized(tail, "VALORADO EN EL LUGAR", "VALORADA EN EL LUGAR", "ATENCION EN SITIO", "ATENCION EN EL SITIO", "ATENCION MEDICA EN SITIO", "ATENCION PREHOSPITALARIA", "PRIMEROS AUXILIOS", "VALORACION PRIMARIA", "SIGNOS VITALES", "INMOVILIZACION", "ESTABILIZACION")
	hasDeath := containsAnyNormalized(tail, "FALLECIO", "PERDIO LA VIDA", "SIN SIGNOS VITALES", "DECESO")
	score := 0.0
	switch code {
	case "17":
		if hasTransfer {
			score -= 28
		}
		if hasMedicalSite && !hasTransfer {
			score += 25
		}
	case "46":
		if !hasTransfer {
			score -= 18
		}
		if hasMedicalSite && hasTransfer && hasHospital {
			score -= 55
		}
		if hasTransfer && hasHospital && !hasMedicalSite {
			score += 25
		}
	case "35":
		if hasTransfer && hasHospital && hasMedicalSite {
			score += 45
		} else {
			score -= 35
		}
	case "19", "47", "48":
		if !hasDeath {
			score -= 30
		}
	}
	return score
}

func analyzeClosure(note Note) ClosureAnalysis {
	full, tail, outcome := closureTextSections(note)
	analysis := ClosureAnalysis{Alternatives: []ClosureCandidate{}, Confidence: "BAJA", Reason: "NO SE ENCONTRÓ EVIDENCIA TEXTUAL SUFICIENTE EN EL RESULTADO DE LA NOTA. SE REQUIERE SELECCIÓN HUMANA."}
	if full == "" {
		return analysis
	}

	decisiveCode, decisiveReason := "", ""
	// Si la narrativa contiene literalmente una definición completa del catálogo,
	// esa coincidencia tiene prioridad absoluta. Esto también permite auditar que los 65 códigos
	// cargados desde el PDF sean reconocibles sin depender de una lista parcial de reglas.
	bestDefinitionLen := 0
	for _, item := range closureCatalog {
		definition := normalizeClosureText(item.Definition)
		definitionLen := len([]rune(definition))
		if definitionLen >= 35 && strings.Contains(outcome, definition) && definitionLen > bestDefinitionLen {
			bestDefinitionLen = definitionLen
			decisiveCode = item.Code
			decisiveReason = "COINCIDENCIA CON LA DEFINICIÓN COMPLETA DEL CÓDIGO DE CIERRE " + item.Code
		}
	}
	if decisiveCode == "" {
		decisiveCode, decisiveReason = decisiveClosure(outcome, outcome+" "+tail, full)
	}
	if decisiveCode == "" {
		decisiveCode, decisiveReason = directStrongClosure(outcome, tail)
	}

	candidates := make([]ClosureCandidate, 0, len(closureCatalog))
	for _, item := range closureCatalog {
		score := 0.0
		evidence := []string{}
		conceptMatches := 0
		nameNeedle := normalizeClosureText(item.Name)
		if nameNeedle != "" {
			if strings.Contains(outcome, nameNeedle) {
				score += 48
				evidence = append(evidence, item.Name)
			} else if strings.Contains(tail, nameNeedle) {
				score += 28
				evidence = append(evidence, item.Name)
			}
		}

		for _, phrase := range item.Strong {
			needle := normalizeClosureText(phrase)
			if needle == "" {
				continue
			}
			if strings.Contains(outcome, needle) {
				score += 38
				evidence = append(evidence, phrase)
			} else if strings.Contains(tail, needle) {
				score += 23
				evidence = append(evidence, phrase)
			} else if strings.Contains(full, needle) {
				score += 7
			}
		}

		for _, concept := range item.Concepts {
			needle := normalizeClosureText(concept)
			if needle == "" {
				continue
			}
			if strings.Contains(outcome, needle) {
				score += 12
				conceptMatches++
				evidence = append(evidence, concept)
			} else if strings.Contains(tail, needle) {
				score += 7
				conceptMatches++
			} else if strings.Contains(full, needle) {
				score += 2
				conceptMatches++
			}
		}
		if len(item.Concepts) > 1 && conceptMatches >= len(item.Concepts) {
			score += 20
		}

		// La definición completa del PDF también participa. Solo se toman palabras
		// distintivas para evitar que frases de trámite como "de acuerdo a las notas" sesguen el resultado.
		definitionTokens := closureTokenSet(item.Definition)
		matchedDefinition := 0
		for token := range definitionTokens {
			if strings.Contains(outcome, token) {
				score += 4.5
				matchedDefinition++
			} else if strings.Contains(tail, token) {
				score += 2.0
				matchedDefinition++
			} else if strings.Contains(full, token) {
				score += .4
			}
		}
		if matchedDefinition >= 3 {
			score += float64(matchedDefinition-2) * 3.5
		}

		score += closureContextAdjustment(item.Code, outcome+" "+tail)
		if item.Code == decisiveCode {
			if score < 165 {
				score = 165
			}
			evidence = append([]string{decisiveReason}, evidence...)
		}
		if score < 0 {
			score = 0
		}
		if len(evidence) > 8 {
			evidence = evidence[:8]
		}
		candidates = append(candidates, ClosureCandidate{Code: item.Code, Name: item.Name, Definition: item.Definition, Score: score, Evidence: evidence})
	}

	sort.Slice(candidates, func(i, j int) bool {
		if candidates[i].Score == candidates[j].Score {
			ci, _ := strconv.Atoi(candidates[i].Code)
			cj, _ := strconv.Atoi(candidates[j].Code)
			return ci < cj
		}
		return candidates[i].Score > candidates[j].Score
	})
	if len(candidates) == 0 || candidates[0].Score < 24 {
		return analysis
	}
	top := candidates[0]
	secondScore := 0.0
	if len(candidates) > 1 {
		secondScore = candidates[1].Score
	}
	margin := top.Score - secondScore
	if decisiveCode != "" && top.Code == decisiveCode {
		analysis.Confidence = "ALTA"
	} else if top.Score >= 92 && margin >= 16 {
		analysis.Confidence = "ALTA"
	} else if top.Score >= 52 && margin >= 9 {
		analysis.Confidence = "MEDIA"
	}
	analysis.Recommended = &top
	if decisiveReason != "" && top.Code == decisiveCode {
		analysis.Reason = decisiveReason
	} else {
		analysis.Reason = fmt.Sprintf("ANÁLISIS %s DEL RESULTADO FINAL: CÓDIGO %s · %s. MARGEN %.1f PUNTOS.", analysis.Confidence, top.Code, top.Name, margin)
	}
	for _, candidate := range candidates {
		if candidate.Score < 14 || len(analysis.Alternatives) >= 6 {
			break
		}
		if candidate.Code == top.Code {
			continue
		}
		analysis.Alternatives = append(analysis.Alternatives, candidate)
	}
	return analysis
}

func analyzeClosureHTTP(w http.ResponseWriter, r *http.Request, s *Store) {
	id, err := strconv.ParseInt(strings.TrimSpace(r.URL.Query().Get("note_id")), 10, 64)
	if err != nil || id <= 0 {
		writeError(w, http.StatusBadRequest, "Identificador de nota inválido.")
		return
	}
	s.mu.RLock()
	var note *Note
	for i := range s.db.Notes {
		if s.db.Notes[i].ID == id {
			copy := s.db.Notes[i]
			note = &copy
			break
		}
	}
	s.mu.RUnlock()
	if note == nil {
		writeError(w, http.StatusNotFound, "La nota no existe.")
		return
	}
	analysis := analyzeClosure(*note)
	writeJSON(w, http.StatusOK, map[string]any{"ok": true, "analysis": analysis})
}

func workflowAction(w http.ResponseWriter, r *http.Request, s *Store) {
	var payload struct {
		NoteID      int64  `json:"noteId"`
		Action      string `json:"action"`
		ClosureCode string `json:"closureCode"`
		RequireCode bool   `json:"requireCode"`
		Observation string `json:"observation"`
	}
	if err := decodeJSON(r, &payload); err != nil {
		writeError(w, http.StatusBadRequest, err.Error())
		return
	}
	if payload.NoteID <= 0 {
		writeError(w, http.StatusBadRequest, "Identificador de nota inválido.")
		return
	}
	operator := dispatcherFromRequest(r)
	if operator == "" {
		writeError(w, http.StatusUnauthorized, "Inicia sesión de despacho para realizar esta acción.")
		return
	}
	action := strings.ToLower(strings.TrimSpace(payload.Action))
	s.mu.Lock()
	index := -1
	for i := range s.db.Notes {
		if s.db.Notes[i].ID == payload.NoteID {
			index = i
			break
		}
	}
	if index < 0 {
		s.mu.Unlock()
		writeError(w, http.StatusNotFound, "La nota no existe.")
		return
	}
	note := &s.db.Notes[index]
	now := nowISO()
	changed := false
	switch action {
	case "open":
		if note.WorkflowStatus == "" || note.WorkflowStatus == statusNew {
			note.WorkflowStatus = statusOpen
			if note.OpenedAt == "" {
				note.OpenedAt = now
			}
			note.UpdatedAt = now
			s.addAuditLocked("ABRIR_NOTA", note.ID, note.Folio, map[string]any{"operador": operator, "ip": clientIP(r)})
			changed = true
		}
	case "used":
		if note.WorkflowStatus == statusClosed {
			s.mu.Unlock()
			writeError(w, http.StatusConflict, "El incidente ya está cerrado.")
			return
		}
		note.WorkflowStatus = statusUsed
		note.UsedAt = now
		note.AutoCloseEligible = false
		note.UpdatedAt = now
		s.addAuditLocked("MARCAR_USADA", note.ID, note.Folio, map[string]any{"operador": operator, "ip": clientIP(r)})
		changed = true
	case "close":
		if note.WorkflowStatus == statusClosed {
			s.mu.Unlock()
			writeError(w, http.StatusConflict, "El incidente ya está cerrado.")
			return
		}
		code := nonDigits.ReplaceAllString(payload.ClosureCode, "")
		if payload.RequireCode && code == "" {
			s.mu.Unlock()
			writeError(w, http.StatusBadRequest, "Selecciona un código de cierre o desmarca Código de cierre obligatorio.")
			return
		}
		closureName := ""
		if code != "" {
			item, ok := closureByCode[code]
			if !ok {
				s.mu.Unlock()
				writeError(w, http.StatusBadRequest, "El código de cierre seleccionado no existe en el catálogo.")
				return
			}
			closureName = item.Name
		}
		note.WorkflowStatus = statusClosed
		note.ClosedAt = now
		note.ClosureCode = code
		note.ClosureName = closureName
		if code == "" {
			note.ClosureMethod = "MANUAL SIN CÓDIGO"
		} else {
			note.ClosureMethod = "MANUAL"
		}
		note.ClosureReason = truncate(strings.TrimSpace(payload.Observation), 500)
		note.AutoCloseEligible = false
		note.UpdatedAt = now
		s.addAuditLocked("CERRAR_INCIDENTE", note.ID, note.Folio, map[string]any{
			"operador": operator, "ip": clientIP(r), "codigo": code, "nombre": closureName,
		})
		changed = true
	default:
		s.mu.Unlock()
		writeError(w, http.StatusBadRequest, "Acción de seguimiento no válida.")
		return
	}
	if changed {
		s.db.Version++
		if err := s.saveLocked(); err != nil {
			s.mu.Unlock()
			writeError(w, http.StatusInternalServerError, err.Error())
			return
		}
	}
	copy := *note
	version := s.db.Version
	s.mu.Unlock()
	writeJSON(w, http.StatusOK, map[string]any{"ok": true, "note": copy, "version": version})
}

func autoCloseLoop(s *Store) {
	ticker := time.NewTicker(15 * time.Second)
	defer ticker.Stop()
	time.Sleep(2 * time.Second)
	autoCloseOnce(s)
	for range ticker.C {
		autoCloseOnce(s)
	}
}

func autoCloseOnce(s *Store) {
	now := time.Now()
	s.mu.Lock()
	changed := false
	for i := range s.db.Notes {
		note := &s.db.Notes[i]
		if !note.AutoCloseEligible || note.UsedAt != "" || note.WorkflowStatus == statusClosed || note.WorkflowStatus == statusUsed {
			continue
		}
		created, err := time.Parse(time.RFC3339, note.CreatedAt)
		if err != nil || now.Sub(created) < autoCloseAfter {
			continue
		}
		analysis := analyzeClosure(*note)
		if analysis.Recommended == nil || analysis.Confidence == "BAJA" {
			continue
		}
		item, ok := closureByCode[analysis.Recommended.Code]
		if !ok {
			continue
		}
		note.WorkflowStatus = statusClosed
		note.ClosedAt = now.Format(time.RFC3339)
		note.ClosureCode = item.Code
		note.ClosureName = item.Name
		note.ClosureMethod = "AUTOMÁTICO 30 MIN"
		note.ClosureReason = analysis.Reason
		note.AutoCloseEligible = false
		note.UpdatedAt = now.Format(time.RFC3339)
		s.addAuditLocked("AUTO_CERRAR_30_MIN", note.ID, note.Folio, map[string]any{
			"operador": "SISTEMA AUTOMÁTICO", "codigo": item.Code, "nombre": item.Name,
		})
		changed = true
	}
	if changed {
		s.db.Version++
		_ = s.saveLocked()
	}
	s.mu.Unlock()
}

func withRecovery(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		defer func() {
			if recovered := recover(); recovered != nil {
				log.Printf("Pánico HTTP: %v", recovered)
				writeError(w, http.StatusInternalServerError, "Ocurrió un error interno.")
			}
		}()
		next.ServeHTTP(w, r)
	})
}

func readLocalStatus(client *http.Client, port int) map[string]any {
	addr := fmt.Sprintf("http://%s:%d/api/status", loopbackHost, port)
	resp, err := client.Get(addr)
	if err != nil {
		return nil
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil
	}
	var data map[string]any
	if err := json.NewDecoder(resp.Body).Decode(&data); err != nil {
		return nil
	}
	return data
}

func stopRunningInstances() {
	client := &http.Client{Timeout: 450 * time.Millisecond}
	stopped := false
	for port := firstPort; port <= lastPort; port++ {
		data := readLocalStatus(client, port)
		if data == nil {
			continue
		}
		app, _ := data["app"].(string)
		family, _ := data["family"].(string)
		isOurApp := app == "sistema-notas-local-v1" || family == appFamily || strings.HasPrefix(app, appFamily+"-")
		if !isOurApp {
			continue
		}

		shutdownURL := fmt.Sprintf("http://%s:%d/api/shutdown", loopbackHost, port)
		req, _ := http.NewRequest(http.MethodPost, shutdownURL, strings.NewReader("{}"))
		req.Header.Set("Content-Type", "application/json")
		if resp, err := client.Do(req); err == nil {
			_ = resp.Body.Close()
			stopped = true
		}
	}
	if stopped {
		time.Sleep(950 * time.Millisecond)
	}
}

func findListener() (net.Listener, int, error) {
	for port := firstPort; port <= lastPort; port++ {
		listener, err := net.Listen("tcp", fmt.Sprintf("%s:%d", bindHost, port))
		if err == nil {
			return listener, port, nil
		}
	}
	return nil, 0, errors.New("No se pudo abrir el servidor local. Cierre otras copias e intente nuevamente.")
}

func requestIsLocal(r *http.Request) bool {
	hostPart, _, err := net.SplitHostPort(r.RemoteAddr)
	if err != nil {
		hostPart = r.RemoteAddr
	}
	ip := net.ParseIP(strings.Trim(hostPart, "[]"))
	return ip != nil && ip.IsLoopback()
}

func networkAddresses(port int) []string {
	seen := map[string]bool{}
	result := []string{}
	ifaces, err := net.Interfaces()
	if err != nil {
		return result
	}
	for _, iface := range ifaces {
		if iface.Flags&net.FlagUp == 0 || iface.Flags&net.FlagLoopback != 0 {
			continue
		}
		addrs, err := iface.Addrs()
		if err != nil {
			continue
		}
		for _, addr := range addrs {
			var ip net.IP
			switch value := addr.(type) {
			case *net.IPNet:
				ip = value.IP
			case *net.IPAddr:
				ip = value.IP
			}
			if ip == nil || ip.IsLoopback() || ip.To4() == nil {
				continue
			}
			address := fmt.Sprintf("http://%s:%d/", ip.String(), port)
			if !seen[address] {
				seen[address] = true
				result = append(result, address)
			}
		}
	}
	sort.Strings(result)
	return result
}

func openBrowser(address string) {
	var cmd *exec.Cmd
	switch runtime.GOOS {
	case "windows":
		cmd = exec.Command("rundll32", "url.dll,FileProtocolHandler", address)
	case "darwin":
		cmd = exec.Command("open", address)
	default:
		cmd = exec.Command("xdg-open", address)
	}
	_ = cmd.Start()
}

func showFatal(message string) {
	log.Printf("Error fatal: %s", message)
	if runtime.GOOS == "windows" {
		_ = exec.Command("mshta", "javascript:alert('"+strings.ReplaceAll(message, "'", "")+"');close()").Run()
	}
}

func init() {
	mime.AddExtensionType(".js", "application/javascript")
	mime.AddExtensionType(".css", "text/css")
	loadEmbeddedCatalogs()
}
