"use strict";

const $ = (selector) => document.querySelector(selector);
const $$ = (selector) => [...document.querySelectorAll(selector)];

const CORPS = {
  PC: { nombre: "Protección Civil", logo: "/assets/pc.png" },
  SPM: { nombre: "Seguridad Pública Municipal", logo: "/assets/spm.png" },
  TRVM: { nombre: "Tránsito Vial Municipal", logo: "/assets/trvm.png" },
  GEVP: { nombre: "Guardia Estatal Vial Preventiva", logo: "/assets/gevp.png" },
  GEP: { nombre: "Guardia Estatal Preventiva", logo: "/assets/gep.png" },
  FRIP: { nombre: "Fuerza de Reacción Inmediata Pakal", logo: "/assets/frip.png" }
};

const STATUS = {
  NUEVO: "NUEVO",
  ABIERTO: "ABIERTO",
  USADO: "USADO",
  CLOSED: "INCIDENTE CERRADO"
};

let notes = [];
let selectedId = null;
let selectedNote = null;
let knownVersion = -1;
let pendingPhotos = [];
let editPendingPhotos = [];
let polling = false;
let searchTimer = null;
let serverInfo = null;
let currentDispatcher = (localStorage.getItem("sni_dispatcher") || "").trim();
let closureCodes = [];
let closureCodeMap = new Map();
let currentClosureAnalysis = null;
let orthographyTimer = null;
let incidentCatalog = [];
let incidentPickerTarget = null;
let municipalityPickerTarget = null;
const photoBlobCache = new Map();

const MUNICIPALITIES = [
  "Amatán", "Chapultenango", "Francisco León", "Huitiupán", "Ixhuatán", "Ixtacomitán",
  "Ixtapangajoya", "Jitotol", "Juárez", "Ocotepec", "Ostuacán", "Pantepec", "Pichucalco",
  "Pueblo Nuevo Solistahuacán", "Rayón", "Reforma", "Sabanilla", "Simojovel", "Solosuchiapa",
  "Sunuapa", "Tapalapa", "Tapilula", "San Andrés Duraznal", "Rincón San Pedro Chamula"
];

function escapeHtml(value) {
  return String(value ?? "")
    .replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;").replaceAll("'", "&#039;");
}

function stripHtml(value) {
  const node = document.createElement("div");
  node.innerHTML = value || "";
  return (node.textContent || "").replace(/\s+/g, " ").trim();
}

function toast(message, type = "ok") {
  const el = document.createElement("div");
  el.className = `toast ${type}`;
  el.textContent = message;
  $("#toasts").append(el);
  setTimeout(() => el.remove(), 4300);
}

async function api(url, options = {}) {
  const headers = options.body instanceof Blob || options.body instanceof File
    ? { ...(options.headers || {}) }
    : { "Content-Type": "application/json", ...(options.headers || {}) };
  if (currentDispatcher) headers["X-Dispatcher"] = currentDispatcher;

  const method = String(options.method || "GET").toUpperCase();
  let requestUrl = url;
  if (method === "GET") {
    const sep = requestUrl.includes("?") ? "&" : "?";
    requestUrl += `${sep}_sync=${Date.now()}_${Math.random().toString(36).slice(2)}`;
  }

  const response = await fetch(requestUrl, {
    cache: "no-store",
    credentials: "same-origin",
    ...options,
    headers
  });
  const contentType = response.headers.get("content-type") || "";
  const data = contentType.includes("application/json") ? await response.json() : null;
  if (!response.ok) throw new Error(data?.error || `Error ${response.status}`);
  return data;
}

function dateParts(date = new Date()) {
  const year = date.getFullYear();
  const month = String(date.getMonth() + 1).padStart(2, "0");
  const day = String(date.getDate()).padStart(2, "0");
  return { year, month, day, key: `${year}${month}${day}` };
}

function updateClock() {
  const now = new Date();
  const parts = dateParts(now);
  $("#folioPrefix").textContent = `REF/${parts.key}/`;
  $("#fecha").value = now.toLocaleDateString("es-MX", { day: "2-digit", month: "2-digit", year: "numeric" });
  $("#hora").value = now.toLocaleTimeString("es-MX", { hour: "numeric", minute: "2-digit", hour12: true });
}

function formatDate(iso) {
  if (!iso) return "";
  const d = new Date(iso);
  return Number.isNaN(d.getTime()) ? "" : d.toLocaleDateString("es-MX", { day: "2-digit", month: "2-digit", year: "numeric" });
}

function formatTime(iso) {
  if (!iso) return "";
  const d = new Date(iso);
  return Number.isNaN(d.getTime()) ? "" : d.toLocaleTimeString("es-MX", { hour: "numeric", minute: "2-digit", second: "2-digit", hour12: true });
}

function formatDateTime(iso) {
  if (!iso) return "Sin dato";
  return `${formatDate(iso)} ${formatTime(iso)}`.trim();
}

function formatBytes(bytes) {
  const n = Number(bytes || 0);
  if (n < 1024) return `${n} B`;
  if (n < 1024 * 1024) return `${(n / 1024).toFixed(0)} KB`;
  return `${(n / 1024 / 1024).toFixed(1)} MB`;
}

function showView(name, updateUrl = true) {
  $$(".view").forEach(v => v.classList.toggle("active", v.id === `${name}View`));
  $$(".nav-btn").forEach(b => b.classList.toggle("active", b.dataset.view === name));
  if (updateUrl) history.replaceState(null, "", `/?vista=${name}`);
  if (name === "dashboard") loadNotes(false);
}

function normalizeFolioInput(input) {
  input.value = input.value.replace(/\D/g, "").slice(0, 20);
}

function siguienteFolio(actual) {
  try {
    const ancho = actual.length;
    const siguiente = (BigInt(actual) + 1n).toString();
    return siguiente.padStart(ancho, "0");
  } catch {
    return "";
  }
}

function setupEditorButtons() {
  $$('[data-cmd]').forEach(button => button.addEventListener("click", () => {
    $("#editorNota").focus();
    document.execCommand(button.dataset.cmd, false, null);
  }));
  $$('[data-edit-cmd]').forEach(button => button.addEventListener("click", () => {
    $("#editContenido").focus();
    document.execCommand(button.dataset.editCmd, false, null);
  }));
}

function photoKey(file) {
  return `${file.name}|${file.size}|${file.lastModified}|${file.type}`;
}

function addFiles(fileList, edit = false) {
  const target = edit ? editPendingPhotos : pendingPhotos;
  const existing = new Set(target.map(item => item.key));
  const files = [...fileList].filter(file => file && file.type.startsWith("image/"));
  let added = 0;
  for (const file of files) {
    if (target.length >= 30) {
      toast("Se permiten hasta 30 fotografías por nota.", "error");
      break;
    }
    if (file.size > 20 * 1024 * 1024) {
      toast(`${file.name || "Una imagen"} supera 20 MB.`, "error");
      continue;
    }
    const key = photoKey(file);
    if (existing.has(key)) continue;
    existing.add(key);
    target.push({ key, file, url: URL.createObjectURL(file) });
    added++;
  }
  renderPendingPhotos(edit);
  if (added) toast(`${added} fotografía${added === 1 ? " agregada" : "s agregadas"}.`);
}

function renderPendingPhotos(edit = false) {
  const target = edit ? editPendingPhotos : pendingPhotos;
  const container = edit ? $("#editPhotoPreview") : $("#photoPreview");
  container.innerHTML = "";
  target.forEach((item, index) => {
    const card = document.createElement("div");
    card.className = "photo-item";
    card.innerHTML = `<img src="${item.url}" alt="Vista previa"><button type="button" title="Quitar">×</button><small>${escapeHtml(item.file.name || "Imagen pegada")} · ${formatBytes(item.file.size)}</small>`;
    card.querySelector("button").addEventListener("click", () => {
      URL.revokeObjectURL(item.url);
      target.splice(index, 1);
      renderPendingPhotos(edit);
    });
    card.querySelector("img").addEventListener("click", () => openLightbox(item.url));
    container.append(card);
  });
}

function setupDropZone(zone, input, chooseButton, edit = false) {
  const openPicker = event => {
    event?.stopPropagation();
    input.click();
  };
  zone.addEventListener("click", event => {
    if (!event.target.closest("button")) openPicker(event);
  });
  chooseButton.addEventListener("click", openPicker);
  input.addEventListener("change", () => {
    addFiles(input.files, edit);
    input.value = "";
  });
  ["dragenter", "dragover"].forEach(type => zone.addEventListener(type, event => {
    event.preventDefault();
    zone.classList.add("dragging");
  }));
  ["dragleave", "drop"].forEach(type => zone.addEventListener(type, event => {
    event.preventDefault();
    zone.classList.remove("dragging");
  }));
  zone.addEventListener("drop", event => addFiles(event.dataTransfer.files, edit));
}

async function uploadPhotos(noteId, photoItems, progressCallback = () => {}) {
  if (!photoItems.length) return [];
  let next = 0;
  let completed = 0;
  const errors = [];
  const workers = Math.min(6, photoItems.length);
  async function worker() {
    while (true) {
      const index = next++;
      if (index >= photoItems.length) return;
      const item = photoItems[index];
      try {
        const url = `/api/photos?note_id=${noteId}&name=${encodeURIComponent(item.file.name || `imagen_${index + 1}`)}`;
        const headers = { "Content-Type": item.file.type || "image/jpeg" };
        if (currentDispatcher) headers["X-Dispatcher"] = currentDispatcher;
        const response = await fetch(url, { method: "POST", headers, body: item.file });
        const data = await response.json();
        if (!response.ok) throw new Error(data.error || "No se pudo guardar una fotografía.");
      } catch (error) {
        errors.push(error.message);
      } finally {
        completed++;
        progressCallback(completed, photoItems.length);
      }
    }
  }
  await Promise.all(Array.from({ length: workers }, worker));
  if (errors.length) throw new Error(`${errors.length} fotografía(s) no se guardaron: ${errors[0]}`);
}

function clearPending(edit = false) {
  const target = edit ? editPendingPhotos : pendingPhotos;
  target.forEach(item => URL.revokeObjectURL(item.url));
  target.length = 0;
  renderPendingPhotos(edit);
}


function normalizeSearchText(value) {
  return String(value || "").normalize("NFD").replace(/[\u0300-\u036f]/g, "").toUpperCase();
}

async function loadIncidentCatalog() {
  try {
    const response = await fetch("/tipificaciones.json?v=3.5.0", { cache: "no-store" });
    if (!response.ok) throw new Error(`Error ${response.status}`);
    const data = await response.json();
    incidentCatalog = Array.isArray(data.items) ? data.items : [];
    window.__incidentCatalogTotal = Number(data.count || incidentCatalog.length);
    if (incidentCatalog.length !== 282 || window.__incidentCatalogTotal !== 282) {
      throw new Error(`Catálogo incompleto: se cargaron ${incidentCatalog.length} de 282 tipificaciones.`);
    }
    const types = [...new Set(incidentCatalog.map(item => item.type).filter(Boolean))];
    const filter = $("#incidentTypeFilter");
    filter.innerHTML = '<option value="">TODOS LOS TIPOS</option>' + types.map(type => `<option value="${escapeHtml(type)}">${escapeHtml(type)}</option>`).join("");
    renderIncidentPicker();
  } catch (error) {
    incidentCatalog = [];
    $("#incidentPickerStatus").textContent = "No se pudo cargar el catálogo de tipificaciones.";
    $("#incidentResults").innerHTML = "";
  }
}

function renderIncidentPicker() {
  const results = $("#incidentResults");
  if (!results) return;
  const query = normalizeSearchText($("#incidentSearch")?.value || "");
  const type = $("#incidentTypeFilter")?.value || "";
  const filtered = incidentCatalog.filter(item => {
    if (type && item.type !== type) return false;
    if (!query) return true;
    return normalizeSearchText(`${item.code} ${item.name} ${item.type} ${item.subtype}`).includes(query);
  });
  const total = Number(window.__incidentCatalogTotal || incidentCatalog.length);
  $("#incidentPickerStatus").textContent = `${filtered.length} de ${total} tipificaciones · CNIE V2.0 completo`;
  results.innerHTML = filtered.length ? filtered.map(item => `
    <button type="button" class="picker-item incident-picker-item" data-incident-code="${escapeHtml(item.code)}">
      <span class="picker-code">${escapeHtml(item.code)}</span>
      <span class="picker-main"><strong>${escapeHtml(item.name)}</strong><small>${escapeHtml(item.type)} · ${escapeHtml(item.subtype)}</small></span>
      <span class="priority-badge priority-${String(item.priority || "").toLowerCase()}">${escapeHtml(item.priority || "")}</span>
    </button>`).join("") : '<div class="picker-empty">No se encontraron tipificaciones con esa búsqueda.</div>';
}

function openIncidentPicker(targetId) {
  incidentPickerTarget = targetId;
  $("#incidentSearch").value = "";
  $("#incidentTypeFilter").value = "";
  renderIncidentPicker();
  $("#incidentModal").classList.add("open");
  setTimeout(() => $("#incidentSearch").focus(), 70);
}

function closeIncidentPicker() {
  $("#incidentModal").classList.remove("open");
  incidentPickerTarget = null;
}

function selectIncident(code) {
  const item = incidentCatalog.find(entry => String(entry.code) === String(code));
  const target = incidentPickerTarget ? document.getElementById(incidentPickerTarget) : null;
  if (!item || !target) return;
  target.value = item.name;
  target.dataset.incidentCode = item.code;
  closeIncidentPicker();
  if (target.id === "titulo") updateOrthographyStatus(`Tipificación ${item.code} seleccionada`, false);
}

function renderMunicipalityPicker() {
  const query = normalizeSearchText($("#municipalitySearch")?.value || "");
  const filtered = MUNICIPALITIES.filter(name => !query || normalizeSearchText(name).includes(query));
  $("#municipalityPickerStatus").textContent = `${filtered.length} municipio${filtered.length === 1 ? "" : "s"}`;
  $("#municipalityResults").innerHTML = filtered.length ? filtered.map(name => `
    <button type="button" class="picker-item municipality-picker-item" data-municipality="${escapeHtml(name)}">
      <span class="municipality-pin">⌖</span>
      <span class="picker-main"><strong>${escapeHtml(name)}</strong><small>Chiapas${name === "Reforma" ? " · SEDE" : ""}</small></span>
      ${name === "Reforma" ? '<span class="site-badge">SEDE</span>' : ''}
    </button>`).join("") : '<div class="picker-empty">No se encontró ese municipio.</div>';
}

function openMunicipalityPicker(targetId) {
  municipalityPickerTarget = targetId;
  $("#municipalitySearch").value = "";
  renderMunicipalityPicker();
  $("#municipalityModal").classList.add("open");
  setTimeout(() => $("#municipalitySearch").focus(), 70);
}

function closeMunicipalityPicker() {
  $("#municipalityModal").classList.remove("open");
  municipalityPickerTarget = null;
}

function selectMunicipality(name) {
  const target = municipalityPickerTarget ? document.getElementById(municipalityPickerTarget) : null;
  if (!target || !MUNICIPALITIES.includes(name)) return;
  target.value = `${name}, Chiapas`;
  closeMunicipalityPicker();
}


function getCaretOffset(root) {
  const sel = window.getSelection?.();
  if (!sel || !sel.rangeCount || !root.contains(sel.anchorNode)) return null;
  const range = sel.getRangeAt(0).cloneRange();
  range.selectNodeContents(root);
  range.setEnd(sel.anchorNode, sel.anchorOffset);
  return range.toString().length;
}

function restoreCaretOffset(root, offset) {
  if (offset === null || offset === undefined) return;
  const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT);
  let remaining = Math.max(0, offset);
  let node;
  while ((node = walker.nextNode())) {
    const length = node.nodeValue?.length || 0;
    if (remaining <= length) {
      const range = document.createRange();
      range.setStart(node, remaining);
      range.collapse(true);
      const sel = window.getSelection();
      sel.removeAllRanges();
      sel.addRange(range);
      return;
    }
    remaining -= length;
  }
  const range = document.createRange();
  range.selectNodeContents(root);
  range.collapse(false);
  const sel = window.getSelection();
  sel.removeAllRanges();
  sel.addRange(range);
}

function updateOrthographyStatus(message = "Ortografía estricta activada · corrige al escribir, pegar, salir y guardar", changed = false) {
  const el = $("#orthographyStatus");
  if (!el) return;
  el.textContent = message;
  el.classList.toggle("corrected", changed);
}

async function applyOrthography(edit = false, quiet = true) {
  const titleEl = edit ? $("#editTitulo") : $("#titulo");
  const editorEl = edit ? $("#editContenido") : $("#editorNota");
  if (!titleEl || !editorEl) return false;
  const originalTitle = titleEl.value;
  const originalHTML = editorEl.innerHTML;
  const caretOffset = document.activeElement === editorEl ? getCaretOffset(editorEl) : null;
  if (!originalTitle.trim() && !stripHtml(originalHTML)) return false;
  try {
    const result = await api("/api/orthography", {
      method: "POST",
      body: JSON.stringify({ title: originalTitle, html: originalHTML })
    });
    // No sobrescribir lo que el operador haya seguido escribiendo mientras respondía el servidor.
    if (titleEl.value !== originalTitle || editorEl.innerHTML !== originalHTML) return false;
    if (result.title !== undefined) titleEl.value = result.title;
    if (result.html !== undefined) {
      editorEl.innerHTML = result.html;
      if (caretOffset !== null) restoreCaretOffset(editorEl, caretOffset);
    }
    if (result.changed) {
      if (!edit) updateOrthographyStatus("Ortografía corregida automáticamente", true);
      if (!quiet) toast("Ortografía corregida automáticamente.");
      return true;
    }
  } catch (error) {
    if (!quiet) toast(`No se pudo previsualizar la corrección: ${error.message}`, "error");
  }
  return false;
}

function scheduleOrthography(edit = false) {
  clearTimeout(orthographyTimer);
  orthographyTimer = setTimeout(() => applyOrthography(edit, true), 1400);
}

function updateSessionUI() {
  const button = $("#sessionBtn");
  if (!button) return;
  if (currentDispatcher) {
    button.textContent = `Despacho: ${currentDispatcher}`;
    button.classList.add("logged-in");
  } else {
    button.textContent = "Despacho: SIN SESIÓN";
    button.classList.remove("logged-in");
  }
}

function openSessionModal() {
  $("#dispatcherName").value = currentDispatcher;
  $("#sessionCancel").hidden = !currentDispatcher;
  $("#sessionModal").classList.add("open");
  setTimeout(() => $("#dispatcherName").focus(), 80);
}

function closeSessionModal() {
  if (!currentDispatcher) return;
  $("#sessionModal").classList.remove("open");
}

function requireDispatcher() {
  if (currentDispatcher) return true;
  openSessionModal();
  toast("Inicia sesión de despacho para continuar.", "error");
  return false;
}

async function saveDispatcherSession(event) {
  event.preventDefault();
  const name = $("#dispatcherName").value.trim().replace(/\s+/g, " ").toUpperCase();
  if (name.length < 2) return toast("Escribe el nombre o clave del despachador.", "error");
  try {
    const result = await api("/api/session", { method: "POST", body: JSON.stringify({ name }) });
    currentDispatcher = result.name || name;
    localStorage.setItem("sni_dispatcher", currentDispatcher);
    updateSessionUI();
    closeSessionModal();
    toast(`Sesión iniciada: ${currentDispatcher}`);
  } catch (error) {
    toast(error.message, "error");
  }
}

async function saveNewNote(event) {
  event.preventDefault();
  if (!requireDispatcher()) return;
  await applyOrthography(false, true);
  const manual = $("#folioManual").value.replace(/\D/g, "").slice(0, 20);
  const title = $("#titulo").value.trim();
  const corporation = $("#corporacion").value;
  const municipality = $("#municipio").value.trim();
  const content = $("#editorNota").innerHTML.trim();
  if (!manual || /^0+$/.test(manual)) return toast("Escriba una terminación de folio válida.", "error");
  if (!title) return toast("Escriba el título del incidente.", "error");
  if (!corporation) return toast("Seleccione la corporación.", "error");
  if (!municipality) return toast("Escriba el municipio.", "error");
  if (stripHtml(content).length < 5) return toast("Escriba el contenido de la nota.", "error");

  const button = $("#saveBtn");
  const progress = $("#saveProgress");
  button.disabled = true;
  button.textContent = "Guardando nota…";
  progress.classList.remove("hidden");
  progress.querySelector("div").style.width = "10%";
  progress.querySelector("span").textContent = "Guardando datos…";

  try {
    const parts = dateParts();
    const created = await api("/api/notes", {
      method: "POST",
      body: JSON.stringify({
        folioManual: manual, fechaClave: parts.key, titulo: title,
        corporacion: corporation, municipio: municipality,
        operador: currentDispatcher, contenidoHtml: content
      })
    });
    progress.querySelector("div").style.width = pendingPhotos.length ? "18%" : "100%";
    if (pendingPhotos.length) {
      button.textContent = "Guardando fotografías…";
      await uploadPhotos(created.id, pendingPhotos, (done, total) => {
        const percent = 18 + Math.round((done / total) * 82);
        progress.querySelector("div").style.width = `${percent}%`;
        progress.querySelector("span").textContent = `Fotografías ${done} de ${total}`;
      });
    }
    toast(created.orthographyCorrected
      ? `Nota ${created.folio} guardada. Ortografía corregida automáticamente.`
      : `Nota ${created.folio} guardada en la base local.`);
    selectedId = null;
    selectedNote = null;
    clearPending(false);
    $("#titulo").value = "";
    $("#editorNota").innerHTML = "";
    $("#folioManual").value = siguienteFolio(manual);
    updateOrthographyStatus();
    knownVersion = Number(created.version ?? -1);
    showView("dashboard");
    await loadNotes(false);
    if (notes.some(note => Number(note.id) === Number(created.id))) {
      await loadSelectedNote(Number(created.id), true);
    } else {
      await new Promise(resolve => setTimeout(resolve, 150));
      await loadNotes(false);
      if (notes.some(note => Number(note.id) === Number(created.id))) {
        await loadSelectedNote(Number(created.id), true);
      }
    }
  } catch (error) {
    toast(error.message, "error");
  } finally {
    button.disabled = false;
    button.textContent = "Agregar Nota Informativa";
    setTimeout(() => progress.classList.add("hidden"), 500);
  }
}

async function loadNotes(keepSelection = true) {
  if (!keepSelection) {
    selectedId = null;
    selectedNote = null;
    renderViewer();
  }
  const query = new URLSearchParams({ q: $("#searchInput").value.trim(), corporation: $("#corpFilter").value });
  try {
    const data = await api(`/api/notes?${query}`);
    notes = data.notes || [];
    if (Number.isFinite(Number(data.version))) knownVersion = Number(data.version);
    if (!keepSelection || !selectedId || !notes.some(n => n.id === selectedId)) {
      selectedId = null;
      selectedNote = null;
    }
    renderNotes();
    if (selectedId) await loadSelectedNote(selectedId, false);
    else renderViewer();
  } catch (error) {
    setConnection(false);
    toast(error.message, "error");
  }
}

function workflowStatusLabel(note) {
  return note.workflowStatus || "ABIERTO";
}

function renderNotes() {
  $("#notesCount").textContent = `${notes.length} nota${notes.length === 1 ? "" : "s"}`;
  const container = $("#notesList");
  container.innerHTML = "";
  if (!notes.length) {
    container.innerHTML = '<div class="no-notes">No hay notas que coincidan con la búsqueda.</div>';
    return;
  }
  for (const note of notes) {
    const corp = CORPS[note.corporacion] || { nombre: note.corporacion, logo: "" };
    const status = workflowStatusLabel(note);
    const card = document.createElement("article");
    card.className = `nota-card${note.id === selectedId ? " selected" : ""}`;
    card.tabIndex = 0;
    card.innerHTML = `
      <div>
        <div class="folio">Folio: ${escapeHtml(note.folio)}</div>
        <div class="titulo">${escapeHtml(note.titulo)}</div>
        <div class="meta">
          <span>Fecha: ${escapeHtml(formatDate(note.createdAt))}</span><span>Municipio: ${escapeHtml(note.municipio)}</span>
          <span>Hora: ${escapeHtml(formatTime(note.createdAt))}</span><span>Corporación: ${escapeHtml(note.corporacion)}</span>
          <span>Registró: ${escapeHtml(note.operador || "SISTEMA")}</span><span>Estado: ${escapeHtml(status)}</span>
        </div>
        <div class="card-badges">
          <span class="workflow-badge ${status === STATUS.CLOSED ? "closed" : status === STATUS.USADO ? "used" : "open"}">${escapeHtml(status)}</span>
          ${note.closureCode ? `<span class="closure-code-badge">CIERRE ${escapeHtml(note.closureCode)}</span>` : ""}
          ${note.photoCount ? `<span class="photo-badge">📷 ${note.photoCount} fotografía${note.photoCount === 1 ? "" : "s"}</span>` : ""}
        </div>
      </div>
      ${corp.logo ? `<img class="card-logo" src="${corp.logo}" alt="${escapeHtml(corp.nombre)}">` : ""}`;
    const select = () => loadSelectedNote(note.id, true);
    card.addEventListener("click", select);
    card.addEventListener("keydown", event => {
      if (event.key === "Enter" || event.key === " ") {
        event.preventDefault();
        select();
      }
    });
    container.append(card);
  }
}

async function loadSelectedNote(id, rerenderList = true) {
  selectedId = id;
  selectedNote = null;
  if (rerenderList) renderNotes();
  renderViewer();

  try {
    const data = await api(`/api/notes/${id}`);
    if (Number(selectedId) !== Number(id)) return;
    if (Number.isFinite(Number(data.version))) knownVersion = Number(data.version);
    selectedNote = data.note;
    if (currentDispatcher && (selectedNote.workflowStatus === STATUS.NUEVO || !selectedNote.workflowStatus)) {
      try {
        const opened = await api("/api/workflow", {
          method: "POST",
          body: JSON.stringify({ noteId: id, action: "open" })
        });
        selectedNote = { ...selectedNote, ...(opened.note || {}) };
        knownVersion = opened.version ?? knownVersion;
      } catch {}
    }
    if (rerenderList) renderNotes();
    renderViewer();
  } catch (error) {
    if (selectedId === id) {
      selectedId = null;
      selectedNote = null;
      renderNotes();
      renderViewer();
    }
    toast(error.message, "error");
  }
}

function cachePhotoForDrag(photo) {
  if (!photo?.url) return;
  if (photoBlobCache.has(photo.url)) return;
  const entry = { file: null, promise: null };
  entry.promise = fetch(photo.url, { cache: "force-cache" })
    .then(response => {
      if (!response.ok) throw new Error("No se pudo preparar la fotografía.");
      return response.blob();
    })
    .then(blob => {
      entry.file = new File([blob], photo.name || "imagen", { type: photo.mime || blob.type || "image/jpeg" });
      return entry.file;
    })
    .catch(() => null);
  photoBlobCache.set(photo.url, entry);
}

function setupDraggablePhoto(img, photo) {
  img.draggable = true;
  const prepare = () => cachePhotoForDrag(photo);
  img.addEventListener("mouseenter", prepare, { once: true });
  img.addEventListener("pointerdown", prepare, { once: true });
  img.addEventListener("dragstart", event => {
    const absolute = new URL(photo.url, location.origin).href;
    const name = (photo.name || `foto_${photo.id || "nota"}.jpg`).replace(/[\r\n:]/g, "_");
    const mime = photo.mime || "image/jpeg";
    event.dataTransfer.effectAllowed = "copy";
    event.dataTransfer.setData("text/uri-list", absolute);
    event.dataTransfer.setData("text/plain", absolute);
    try { event.dataTransfer.setData("DownloadURL", `${mime}:${name}:${absolute}`); } catch {}
    const cached = photoBlobCache.get(photo.url);
    if (cached?.file && event.dataTransfer.items?.add) {
      try { event.dataTransfer.items.add(cached.file); } catch {}
    }
    img.classList.add("drag-source");
  });
  img.addEventListener("dragend", () => img.classList.remove("drag-source"));
}

function renderViewer() {
  const viewer = $("#viewer");
  const panel = $("#viewerPanel");
  const enabled = Boolean(selectedNote && selectedNote.id === selectedId);
  panel?.classList.toggle("no-selection", !enabled);
  const closed = enabled && selectedNote.workflowStatus === STATUS.CLOSED;
  const used = enabled && selectedNote.workflowStatus === STATUS.USADO;
  $("#editBtn").disabled = !enabled || closed;
  $("#usedBtn").disabled = !enabled || closed || used;
  $("#closeIncidentBtn").disabled = !enabled || closed;
  $("#printBtn").disabled = !enabled;
  $("#deleteBtn").disabled = !enabled;
  if (!enabled) {
    viewer.innerHTML = '<div class="empty-view">Selecciona una nota para ver su contenido</div>';
    return;
  }
  const corp = CORPS[selectedNote.corporacion] || { nombre: selectedNote.corporacion };
  const status = workflowStatusLabel(selectedNote);
  const closure = closed
    ? `<div class="viewer-closure"><strong>INCIDENTE CERRADO</strong><span>${selectedNote.closureCode ? `Código ${escapeHtml(selectedNote.closureCode)} · ${escapeHtml(selectedNote.closureName || "")}` : "Cierre sin código"}</span><small>${escapeHtml(selectedNote.closureMethod || "MANUAL")} · ${escapeHtml(formatDateTime(selectedNote.closedAt))}</small></div>`
    : "";
  const gallery = selectedNote.photos?.length
    ? `<div class="gallery-head"><strong>Fotografías</strong><span>Haz clic para ampliar o arrastra una foto hacia otra página para agregarla.</span></div><div class="gallery">${selectedNote.photos.map(photo => `<figure class="draggable-photo"><img src="${photo.url}" data-photo-id="${photo.id}" data-full="${photo.url}" alt="${escapeHtml(photo.name)}" loading="lazy" draggable="true"><figcaption>Arrastra esta foto</figcaption></figure>`).join("")}</div>`
    : "";
  viewer.innerHTML = `
    <h2 class="viewer-title">NOTA INFORMATIVA</h2>
    <div class="viewer-meta"><strong>${escapeHtml(selectedNote.folio)}</strong> · ${escapeHtml(selectedNote.titulo)}<br>
      ${escapeHtml(formatDate(selectedNote.createdAt))}, ${escapeHtml(formatTime(selectedNote.createdAt))} ·
      ${escapeHtml(selectedNote.municipio)} · ${escapeHtml(corp.nombre)}<br>
      <strong>Registró:</strong> ${escapeHtml(selectedNote.operador || "SISTEMA")} · <strong>Estado:</strong> ${escapeHtml(status)}</div>
    ${closure}
    <div class="viewer-content">${selectedNote.contenidoHtml}</div>${gallery}`;
  viewer.querySelectorAll(".gallery img").forEach(img => {
    const photo = selectedNote.photos.find(item => String(item.id) === String(img.dataset.photoId));
    if (!photo) return;
    img.addEventListener("click", () => openLightbox(img.dataset.full));
    setupDraggablePhoto(img, photo);
  });
}

function openLightbox(url) {
  $("#lightboxImage").src = url;
  $("#lightbox").classList.add("open");
}

function closeLightbox() {
  $("#lightbox").classList.remove("open");
  $("#lightboxImage").src = "";
}

function openEditModal() {
  if (!selectedNote || !requireDispatcher()) return;
  if (selectedNote.workflowStatus === STATUS.CLOSED) return toast("El incidente ya está cerrado.", "error");
  clearPending(true);
  $("#editFolio").value = selectedNote.folioManual;
  $("#editTitulo").value = selectedNote.titulo;
  $("#editCorporacion").value = selectedNote.corporacion;
  $("#editMunicipio").value = selectedNote.municipio;
  $("#editContenido").innerHTML = selectedNote.contenidoHtml;
  renderExistingPhotos();
  $("#editModal").classList.add("open");
}

function closeEditModal() {
  $("#editModal").classList.remove("open");
  clearPending(true);
}

function renderExistingPhotos() {
  const container = $("#existingPhotos");
  container.innerHTML = "";
  for (const photo of selectedNote?.photos || []) {
    const card = document.createElement("div");
    card.className = "existing-photo";
    card.innerHTML = `<img src="${photo.url}" alt="${escapeHtml(photo.name)}"><button type="button" title="Eliminar fotografía">×</button>`;
    card.querySelector("img").addEventListener("click", () => openLightbox(photo.url));
    card.querySelector("button").addEventListener("click", async () => {
      if (!requireDispatcher()) return;
      if (!confirm("¿Eliminar esta fotografía de la nota?")) return;
      try {
        await api(`/api/photos/${photo.id}`, { method: "DELETE" });
        await loadSelectedNote(selectedId, false);
        renderExistingPhotos();
        knownVersion = -1;
        toast("Fotografía eliminada.");
      } catch (error) { toast(error.message, "error"); }
    });
    container.append(card);
  }
}

async function saveEditedNote(event) {
  event.preventDefault();
  if (!selectedNote || !requireDispatcher()) return;
  await applyOrthography(true, true);
  const button = $("#saveEdit");
  button.disabled = true;
  button.textContent = "Guardando…";
  try {
    const result = await api(`/api/notes/${selectedNote.id}`, {
      method: "PUT",
      body: JSON.stringify({
        folioManual: $("#editFolio").value,
        titulo: $("#editTitulo").value.trim(),
        corporacion: $("#editCorporacion").value,
        municipio: $("#editMunicipio").value.trim(),
        operador: selectedNote.operador,
        contenidoHtml: $("#editContenido").innerHTML.trim()
      })
    });
    if (editPendingPhotos.length) {
      button.textContent = "Guardando fotos…";
      await uploadPhotos(selectedNote.id, editPendingPhotos);
    }
    clearPending(true);
    knownVersion = -1;
    await loadNotes(true);
    closeEditModal();
    toast(result.orthographyCorrected ? "Cambios guardados y ortografía corregida." : "Cambios guardados.");
  } catch (error) {
    toast(error.message, "error");
  } finally {
    button.disabled = false;
    button.textContent = "Guardar cambios";
  }
}

async function deleteSelectedNote() {
  if (!selectedNote || !requireDispatcher()) return;
  if (!confirm(`¿Eliminar definitivamente la nota ${selectedNote.folio}?\n\nTambién se eliminarán sus fotografías.`)) return;
  try {
    const deletingId = Number(selectedNote.id);
    const deleted = await api(`/api/notes/${deletingId}`, { method: "DELETE" });

    notes = notes.filter(note => Number(note.id) !== deletingId);
    selectedId = null;
    selectedNote = null;
    if (Number.isFinite(Number(deleted.version))) knownVersion = Number(deleted.version);
    renderNotes();
    renderViewer();

    await loadNotes(false);
    if (notes.some(note => Number(note.id) === deletingId)) {
      throw new Error("La nota sigue apareciendo en el servidor. Se detectó otra instancia o una base distinta.");
    }
    toast("Nota eliminada de la base local y sincronizada.");
  } catch (error) { toast(error.message, "error"); }
}

async function markSelectedUsed() {
  if (!selectedNote || !requireDispatcher()) return;
  if (selectedNote.workflowStatus === STATUS.CLOSED) return toast("El incidente ya está cerrado.", "error");
  if (!confirm(`¿Marcar la nota ${selectedNote.folio} como USADA?\n\nAl marcarla como usada ya no se cerrará automáticamente a los 30 minutos.`)) return;
  try {
    const result = await api("/api/workflow", {
      method: "POST",
      body: JSON.stringify({ noteId: selectedNote.id, action: "used" })
    });
    selectedNote = { ...selectedNote, ...(result.note || {}) };
    knownVersion = -1;
    await loadNotes(true);
    toast("Nota marcada como USADA. Se desactivó el cierre automático.");
  } catch (error) { toast(error.message, "error"); }
}

async function loadClosureCodes() {
  try {
    const data = await api("/api/closure-codes");
    closureCodes = data.codes || [];
    if (closureCodes.length !== 65) throw new Error(`Catálogo incompleto: se cargaron ${closureCodes.length} de 65 códigos.`);
    closureCodeMap = new Map(closureCodes.map(item => [String(item.code), item]));
    $("#closureDefinition").textContent = `${closureCodes.length} códigos de cierre verificados y cargados. Puedes cerrar sin código si la obligatoriedad está desmarcada.`;
    const select = $("#closureCodeSelect");
    select.innerHTML = '<option value="">SIN CÓDIGO</option>' + closureCodes
      .slice().sort((a, b) => Number(a.code) - Number(b.code))
      .map(item => `<option value="${escapeHtml(item.code)}">${escapeHtml(item.code)} — ${escapeHtml(item.name)}</option>`).join("");
  } catch (error) {
    toast(`No se pudo cargar el catálogo de cierres: ${error.message}`, "error");
  }
}

function updateClosureDefinition() {
  const code = $("#closureCodeSelect").value;
  const item = closureCodeMap.get(code);
  $("#closureDefinition").textContent = item
    ? `${item.code} — ${item.name}. ${item.definition || ""}`
    : "Sin código seleccionado. Puedes cerrar así mientras Código de cierre obligatorio esté desmarcado.";
  const required = $("#closureRequired").checked;
  const button = $("#confirmClosure");
  button.textContent = !code && !required ? "Cerrar sin código" : "Cerrar incidente";
  $("#closureRequired").closest(".checkbox-label").classList.toggle("required-on", required);
}

function renderClosureAnalysis(analysis) {
  currentClosureAnalysis = analysis || null;
  const box = $("#closureSuggestion");
  const recommended = analysis?.recommended;
  if (!recommended) {
    box.innerHTML = `<div class="closure-no-suggestion"><strong>Sin sugerencia confiable</strong><span>${escapeHtml(analysis?.reason || "Selecciona el código manualmente o cierra sin código.")}</span></div>`;
  } else {
    const alternatives = (analysis.alternatives || []).filter(item => item.code !== recommended.code).slice(0, 4);
    box.innerHTML = `
      <div class="closure-recommended">
        <div><span class="closure-confidence">CONFIANZA ${escapeHtml(analysis.confidence || "BAJA")}</span><strong>Código ${escapeHtml(recommended.code)} — ${escapeHtml(recommended.name)}</strong><p>${escapeHtml(analysis.reason || recommended.definition || "")}</p></div>
        <button id="useSuggestedClosure" type="button" class="btn primary">Usar código ${escapeHtml(recommended.code)}</button>
      </div>
      ${alternatives.length ? `<div class="closure-alternatives"><span>Otras coincidencias:</span>${alternatives.map(item => `<button type="button" data-alt-code="${escapeHtml(item.code)}">${escapeHtml(item.code)} · ${escapeHtml(item.name)}</button>`).join("")}</div>` : ""}`;
    $("#useSuggestedClosure")?.addEventListener("click", () => {
      $("#closureCodeSelect").value = String(recommended.code);
      updateClosureDefinition();
    });
    box.querySelectorAll("[data-alt-code]").forEach(button => button.addEventListener("click", () => {
      $("#closureCodeSelect").value = button.dataset.altCode;
      updateClosureDefinition();
    }));
  }
  $("#closureCodeSelect").value = "";
  $("#closureRequired").checked = false;
  $("#closureObservation").value = "";
  updateClosureDefinition();
}

async function openClosureModal() {
  if (!selectedNote || !requireDispatcher()) return;
  if (selectedNote.workflowStatus === STATUS.CLOSED) return toast("El incidente ya está cerrado.", "error");
  $("#closureModal").classList.add("open");
  $("#closureLoading").classList.remove("hidden");
  $("#closureForm").classList.add("hidden");
  try {
    const data = await api(`/api/closure-analysis?note_id=${selectedNote.id}`);
    renderClosureAnalysis(data.analysis);
    $("#closureLoading").classList.add("hidden");
    $("#closureForm").classList.remove("hidden");
  } catch (error) {
    closeClosureModal();
    toast(error.message, "error");
  }
}

function closeClosureModal() {
  $("#closureModal").classList.remove("open");
  currentClosureAnalysis = null;
}

async function submitClosure(event) {
  event.preventDefault();
  if (!selectedNote || !requireDispatcher()) return;
  const code = $("#closureCodeSelect").value;
  const required = $("#closureRequired").checked;
  if (required && !code) return toast("Selecciona un código porque marcaste Código de cierre obligatorio.", "error");
  const item = closureCodeMap.get(code);
  const label = item ? `${item.code} — ${item.name}` : "SIN CÓDIGO";
  if (!confirm(`¿Confirmas el cierre de ${selectedNote.folio}?\n\nCIERRE: ${label}`)) return;
  const button = $("#confirmClosure");
  button.disabled = true;
  button.textContent = "Cerrando…";
  try {
    const result = await api("/api/workflow", {
      method: "POST",
      body: JSON.stringify({
        noteId: selectedNote.id,
        action: "close",
        closureCode: code,
        requireCode: required,
        observation: $("#closureObservation").value.trim()
      })
    });
    selectedNote = { ...selectedNote, ...(result.note || {}) };
    closeClosureModal();
    knownVersion = -1;
    await loadNotes(true);
    toast(code ? `Incidente cerrado con código ${code}.` : "Incidente cerrado sin código de cierre.");
  } catch (error) {
    toast(error.message, "error");
  } finally {
    button.disabled = false;
    updateClosureDefinition();
  }
}

function auditActionLabel(action) {
  const labels = {
    INICIAR_SERVIDOR: "Servidor iniciado",
    INICIAR_SESION: "Inicio de sesión",
    CREAR_NOTA: "Nota registrada",
    EDITAR_NOTA: "Nota editada",
    ABRIR_NOTA: "Nota abierta",
    MARCAR_USADA: "Nota marcada usada",
    CERRAR_INCIDENTE: "Incidente cerrado",
    AUTO_CERRAR_30_MIN: "Cierre automático 30 min",
    AGREGAR_FOTO: "Fotografía agregada",
    ELIMINAR_FOTO: "Fotografía eliminada",
    ELIMINAR_NOTA: "Nota eliminada"
  };
  return labels[action] || action;
}

async function loadAudit() {
  try {
    const data = await api("/api/audit?limit=120");
    const starter = [...(data.audit || [])].find(item => item.action === "INICIAR_SERVIDOR");
    const details = starter?.details || {};
    $("#serverStarterCard").innerHTML = `
      <div><span>Servidor iniciado</span><strong>${escapeHtml(formatDateTime(starter?.createdAt || data.serverStartedAt))}</strong></div>
      <div><span>Usuario de Windows</span><strong>${escapeHtml(details.usuarioSO || data.serverOSUser || "Sin dato")}</strong></div>
      <div><span>Computadora</span><strong>${escapeHtml(details.pc || data.serverHostName || "Sin dato")}</strong></div>`;
    const list = $("#auditList");
    list.innerHTML = "";
    const movements = (data.audit || []).filter(item => item.action !== "INICIAR_SERVIDOR");
    if (!movements.length) {
      list.innerHTML = '<div class="audit-empty">Aún no hay movimientos registrados.</div>';
      return;
    }
    for (const item of movements) {
      const d = item.details || {};
      const row = document.createElement("article");
      row.className = "audit-row";
      const operator = d.operador || d.usuarioSO || "SISTEMA";
      const extra = [item.folio, d.codigo ? `Código ${d.codigo}` : "", d.ip ? `IP ${d.ip}` : ""].filter(Boolean).join(" · ");
      row.innerHTML = `<div><strong>${escapeHtml(auditActionLabel(item.action))}</strong><span>${escapeHtml(operator)}</span>${extra ? `<small>${escapeHtml(extra)}</small>` : ""}</div><time>${escapeHtml(formatDateTime(item.createdAt))}</time>`;
      list.append(row);
    }
  } catch (error) {
    $("#auditList").innerHTML = `<div class="audit-empty">${escapeHtml(error.message)}</div>`;
  }
}

function openSupervision() {
  $("#supervisionModal").classList.add("open");
  loadAudit();
}

function closeSupervision() {
  $("#supervisionModal").classList.remove("open");
}

function setConnection(online) {
  const el = $("#localStatus");
  el.classList.toggle("online", online);
  el.classList.toggle("offline", !online);
  if (!online) {
    el.textContent = "Sin conexión con la computadora servidor";
    return;
  }
  el.textContent = serverInfo?.localRequest
    ? "Servidor central activo"
    : "Conectado al servidor central";
}

async function loadServerInfo() {
  try {
    serverInfo = await api("/api/status");
    setConnection(true);
    const shutdownButton = $("#shutdownBtn");
    if (shutdownButton) shutdownButton.hidden = !serverInfo.localRequest;
    const copyButton = $("#copyLink");
    if (copyButton) {
      copyButton.title = serverInfo.localRequest
        ? "Copia este enlace y ábrelo en la segunda computadora"
        : "Copiar la dirección del servidor central";
    }
  } catch {
    setConnection(false);
  }
}

async function copyServerLink() {
  const urls = serverInfo?.serverUrls || [];
  const link = serverInfo?.localRequest ? (urls[0] || location.origin + "/") : (location.origin + "/");
  if (!link || link.includes("127.0.0.1") || link.includes("localhost")) {
    toast("No se detectó una dirección de red. Verifica que ambas computadoras estén conectadas a la misma red.", "error");
    return;
  }
  try {
    await navigator.clipboard.writeText(link);
    toast(`Enlace copiado: ${link}`);
  } catch {
    window.prompt("Copia este enlace y ábrelo en la segunda computadora:", link);
  }
}

async function pollState() {
  if (polling) return;
  polling = true;
  try {
    const state = await api("/api/state");
    setConnection(true);
    if (knownVersion !== state.version) {
      const first = knownVersion === -1;
      knownVersion = state.version;
      await loadNotes(!first);
      if ($("#supervisionModal").classList.contains("open")) loadAudit();
    }
  } catch {
    setConnection(false);
  } finally {
    polling = false;
  }
}

function setupPaste() {
  document.addEventListener("paste", event => {
    const images = [...(event.clipboardData?.items || [])]
      .filter(item => item.kind === "file" && item.type.startsWith("image/"))
      .map(item => item.getAsFile()).filter(Boolean);
    if (images.length) {
      event.preventDefault();
      addFiles(images, $("#editModal").classList.contains("open"));
      return;
    }
    const inEditor = event.target.closest?.("#editorNota, #editContenido, #titulo, #editTitulo");
    if (inEditor) setTimeout(() => scheduleOrthography($("#editModal").classList.contains("open")), 120);
  });
}

async function shutdown() {
  if (!serverInfo?.localRequest) return toast("Solo la computadora servidor puede cerrar el sistema.", "error");
  if (!confirm("¿Cerrar el servidor central? La segunda computadora perderá la conexión hasta que vuelvas a abrirlo.")) return;
  try { await api("/api/shutdown", { method: "POST", body: JSON.stringify({}) }); } catch {}
  document.body.innerHTML = '<div style="font-family:Segoe UI,Arial;padding:50px;text-align:center"><h2>Sistema cerrado</h2><p>Ya puedes cerrar esta pestaña. Para abrirlo de nuevo, ejecuta <b>SistemaNotas.exe</b>.</p></div>';
  try { window.close(); } catch {}
}

function init() {
  updateClock();
  setInterval(updateClock, 1000);
  setupEditorButtons();
  setupDropZone($("#dropZone"), $("#photoInput"), $("#choosePhotos"), false);
  setupDropZone($("#editDropZone"), $("#editPhotoInput"), $("#editChoosePhotos"), true);
  setupPaste();
  $("#correctNowBtn").addEventListener("click", async () => {
    const changed = await applyOrthography(false, false);
    if (!changed) toast("La nota no requiere correcciones detectables.");
  });
  $("#editorNota").addEventListener("paste", () => setTimeout(() => applyOrthography(false, true), 320));
  $("#editContenido").addEventListener("paste", () => setTimeout(() => applyOrthography(true, true), 320));
  $("#editorNota").addEventListener("input", () => scheduleOrthography(false));
  $("#editContenido").addEventListener("input", () => scheduleOrthography(true));
  $("#editorNota").addEventListener("blur", () => applyOrthography(false, true));
  $("#editContenido").addEventListener("blur", () => applyOrthography(true, true));
  updateSessionUI();
  loadIncidentCatalog();
  renderMunicipalityPicker();

  [["titulo", "titulo"], ["editTitulo", "editTitulo"]].forEach(([id, target]) => {
    const el = document.getElementById(id);
    el.addEventListener("click", () => openIncidentPicker(target));
    el.addEventListener("keydown", event => { if (event.key === "Enter" || event.key === " ") { event.preventDefault(); openIncidentPicker(target); } });
  });
  [["municipio", "municipio"], ["editMunicipio", "editMunicipio"]].forEach(([id, target]) => {
    const el = document.getElementById(id);
    el.addEventListener("click", () => openMunicipalityPicker(target));
    el.addEventListener("keydown", event => { if (event.key === "Enter" || event.key === " ") { event.preventDefault(); openMunicipalityPicker(target); } });
  });
  $("#incidentSearch").addEventListener("input", renderIncidentPicker);
  $("#incidentTypeFilter").addEventListener("change", renderIncidentPicker);
  $("#incidentResults").addEventListener("click", event => {
    const button = event.target.closest("[data-incident-code]");
    if (button) selectIncident(button.dataset.incidentCode);
  });
  $("#closeIncidentPicker").addEventListener("click", closeIncidentPicker);
  $("#incidentModal").addEventListener("click", event => { if (event.target.id === "incidentModal") closeIncidentPicker(); });
  $("#municipalitySearch").addEventListener("input", renderMunicipalityPicker);
  $("#municipalityResults").addEventListener("click", event => {
    const button = event.target.closest("[data-municipality]");
    if (button) selectMunicipality(button.dataset.municipality);
  });
  $("#closeMunicipalityPicker").addEventListener("click", closeMunicipalityPicker);
  $("#municipalityModal").addEventListener("click", event => { if (event.target.id === "municipalityModal") closeMunicipalityPicker(); });

  $$(".nav-btn").forEach(button => button.addEventListener("click", () => showView(button.dataset.view)));
  $("#noteForm").addEventListener("submit", saveNewNote);
  $("#folioManual").addEventListener("input", event => normalizeFolioInput(event.target));
  $("#editFolio").addEventListener("input", event => normalizeFolioInput(event.target));
  $("#searchInput").addEventListener("input", () => {
    clearTimeout(searchTimer);
    searchTimer = setTimeout(() => loadNotes(false), 220);
  });
  $("#corpFilter").addEventListener("change", () => loadNotes(false));
  $("#refreshBtn").addEventListener("click", () => { knownVersion = -1; pollState(); });
  $("#editBtn").addEventListener("click", openEditModal);
  $("#usedBtn").addEventListener("click", markSelectedUsed);
  $("#closeIncidentBtn").addEventListener("click", openClosureModal);
  $("#printBtn").addEventListener("click", () => window.print());
  $("#deleteBtn").addEventListener("click", deleteSelectedNote);
  $("#editForm").addEventListener("submit", saveEditedNote);
  $("#closeEdit").addEventListener("click", closeEditModal);
  $("#cancelEdit").addEventListener("click", closeEditModal);
  $("#editModal").addEventListener("click", event => { if (event.target.id === "editModal") closeEditModal(); });
  $("#sessionBtn").addEventListener("click", openSessionModal);
  $("#sessionForm").addEventListener("submit", saveDispatcherSession);
  $("#sessionCancel").addEventListener("click", closeSessionModal);
  $("#supervisionBtn").addEventListener("click", openSupervision);
  $("#closeSupervision").addEventListener("click", closeSupervision);
  $("#refreshAudit").addEventListener("click", loadAudit);
  $("#supervisionModal").addEventListener("click", event => { if (event.target.id === "supervisionModal") closeSupervision(); });
  $("#closureForm").addEventListener("submit", submitClosure);
  $("#closeClosureModal").addEventListener("click", closeClosureModal);
  $("#cancelClosure").addEventListener("click", closeClosureModal);
  $("#closureModal").addEventListener("click", event => { if (event.target.id === "closureModal") closeClosureModal(); });
  $("#closureCodeSelect").addEventListener("change", updateClosureDefinition);
  $("#closureRequired").addEventListener("change", updateClosureDefinition);
  $("#lightbox").addEventListener("click", event => { if (event.target.id === "lightbox" || event.target.id === "closeLightbox") closeLightbox(); });
  $("#closeLightbox").addEventListener("click", closeLightbox);
  $("#openWindow").addEventListener("click", () => window.open(`${location.origin}/?vista=dashboard`, "_blank"));
  $("#copyLink").addEventListener("click", copyServerLink);
  $("#shutdownBtn").addEventListener("click", shutdown);

  [$("#titulo"), $("#editorNota")].forEach(el => {
    el.addEventListener("blur", () => applyOrthography(false, true));
  });
  [$("#editTitulo"), $("#editContenido")].forEach(el => {
    el.addEventListener("blur", () => applyOrthography(true, true));
  });

  document.addEventListener("keydown", event => {
    if (event.key === "Escape") {
      closeLightbox();
      if ($("#editModal").classList.contains("open")) closeEditModal();
      if ($("#closureModal").classList.contains("open")) closeClosureModal();
      if ($("#supervisionModal").classList.contains("open")) closeSupervision();
      if ($("#sessionModal").classList.contains("open") && currentDispatcher) closeSessionModal();
      if ($("#incidentModal").classList.contains("open")) closeIncidentPicker();
      if ($("#municipalityModal").classList.contains("open")) closeMunicipalityPicker();
    }
  });

  const initial = new URLSearchParams(location.search).get("vista") === "dashboard" ? "dashboard" : "registro";
  showView(initial, false);
  loadServerInfo();
  loadClosureCodes();
  pollState();
  setInterval(pollState, 850);

  if (!currentDispatcher) setTimeout(openSessionModal, 450);
}

init();
