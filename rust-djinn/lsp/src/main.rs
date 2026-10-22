//! rust-djinn-lsp — a language server for Djinn specifications inside Rust
//! files. It runs beside rust-analyzer (the editor attaches both to Rust
//! documents) and only acts on a crate's configured spec file.
//!
//! What it provides, and the LSP mechanism used:
//!   proof status per declaration      inlay hint at the end of the `fn` line (small, always on)
//!                                     + a code lens above it (clickable: open obligations)
//!   smoke-test as a linter            textDocument/publishDiagnostics on open/change/save
//!                                     (debounced), with the conflicting statements linked
//!                                     through relatedInformation
//!   implement / verify / smoke-test   workspace/executeCommand with $/progress reports and a
//!                                     final window/showMessage; lenses and hints refresh after
//!   jump to the obligations / proofs  window/showDocument at the theorem's line
//!
//! LSP has no way to render text on its own line below a function; inlay
//! hints (inline) and code lenses (above) are the standard substitutes.

use cargo_djinn::config::{load_config, Config};
use cargo_djinn::smoke::{self, CheckStatus, SmokeReport};
use cargo_djinn::status::{self, ObState};
use cargo_djinn::verify;
use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::*;
use serde_json::{json, Value};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

const COMMANDS: &[&str] = &[
    "djinn.implement",
    "djinn.verify",
    "djinn.smokeTest",
    "djinn.status",
    "djinn.openObligations",
    "djinn.openProofs",
    "djinn.openGuide",
];

struct Doc {
    text: String,
    version: i32,
}

#[derive(Default)]
struct State {
    docs: HashMap<String, Doc>,
    /// latest smoke report per document uri
    smoke: HashMap<String, SmokeReport>,
    /// generation counter per document, to drop stale lint results
    gen: HashMap<String, u64>,
}

#[derive(Clone)]
struct Ctx {
    sender: crossbeam_sender::Sender,
    state: Arc<Mutex<State>>,
    ids: Arc<AtomicU64>,
    bin: PathBuf,
}

/// A tiny wrapper so the worker threads can send protocol messages.
mod crossbeam_sender {
    pub type Sender = crossbeam_channel::Sender<lsp_server::Message>;
}

impl Ctx {
    fn notify<N: lsp_types::notification::Notification>(&self, params: N::Params) {
        let _ = self.sender.send(Message::Notification(Notification::new(N::METHOD.to_string(), params)));
    }
    fn request<R: lsp_types::request::Request>(&self, params: R::Params) -> RequestId {
        let id = RequestId::from(self.ids.fetch_add(1, Ordering::SeqCst) as i32 + 1_000_000);
        let _ = self.sender.send(Message::Request(Request::new(id.clone(), R::METHOD.to_string(), params)));
        id
    }
    fn log(&self, msg: impl Into<String>) {
        self.notify::<notification::LogMessage>(LogMessageParams { typ: MessageType::LOG, message: msg.into() });
    }
    fn show(&self, typ: MessageType, msg: impl Into<String>) {
        self.notify::<notification::ShowMessage>(ShowMessageParams { typ, message: msg.into() });
    }
    fn refresh(&self) {
        let _ = self.request::<request::CodeLensRefresh>(());
        let _ = self.request::<request::InlayHintRefreshRequest>(());
    }
}

fn main() -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    let (connection, _io_threads) = Connection::stdio();
    let caps = ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Options(TextDocumentSyncOptions {
            open_close: Some(true),
            change: Some(TextDocumentSyncKind::FULL),
            save: Some(TextDocumentSyncSaveOptions::SaveOptions(SaveOptions { include_text: Some(true) })),
            ..Default::default()
        })),
        code_lens_provider: Some(CodeLensOptions { resolve_provider: Some(false) }),
        inlay_hint_provider: Some(OneOf::Left(true)),
        execute_command_provider: Some(ExecuteCommandOptions {
            commands: COMMANDS.iter().map(|s| s.to_string()).collect(),
            work_done_progress_options: Default::default(),
        }),
        ..Default::default()
    };
    // `Connection::initialize` wraps its argument as the capabilities; to also
    // send serverInfo, answer the initialize request ourselves.
    let (init_id, _init_params) = connection.initialize_start()?;
    connection.initialize_finish(
        init_id,
        json!({
            "capabilities": caps,
            "serverInfo": { "name": "rust-djinn-lsp", "version": env!("CARGO_PKG_VERSION") }
        }),
    )?;
    let bin = std::env::var("DJINN_BIN")
        .map(PathBuf::from)
        .unwrap_or_else(|_| std::env::current_exe().ok().and_then(|p| p.parent().map(|d| d.join("cargo-djinn"))).unwrap_or_else(|| PathBuf::from("cargo-djinn")));
    let ctx = Ctx { sender: connection.sender.clone(), state: Arc::new(Mutex::new(State::default())), ids: Arc::new(AtomicU64::new(0)), bin };
    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req)? {
                    break;
                }
                handle_request(&ctx, req);
            }
            Message::Notification(n) => handle_notification(&ctx, n),
            Message::Response(_) => {}
        }
    }
    // The client is gone (shutdown, or its pipe closed). Do not wait for the
    // I/O threads: background lint/driver threads hold clones of the sender,
    // so the writer would never finish and the server would linger forever
    // (as orphaned `rust-djinn-lsp` processes did after the editor closed).
    drop(ctx);
    std::process::exit(0);
}

// ------------------------------------------------------------------ helpers

fn uri_to_path(uri: &Uri) -> PathBuf {
    let s = uri.as_str();
    let p = s.strip_prefix("file://").unwrap_or(s);
    // percent-decoding of the common cases
    let mut out = String::new();
    let b = p.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'%' && i + 2 < b.len() {
            if let Ok(v) = u8::from_str_radix(&p[i + 1..i + 3], 16) {
                out.push(v as char);
                i += 3;
                continue;
            }
        }
        out.push(b[i] as char);
        i += 1;
    }
    PathBuf::from(out)
}

fn path_to_uri(p: &Path) -> Option<Uri> {
    let s = p.to_string_lossy().replace(' ', "%20");
    Uri::from_str(&format!("file://{s}")).ok()
}

/// The crate configuration for a document, if the document is one of its
/// specification files — or, without a manual `spec` setting, a file under
/// `src/` whose buffer has a `djinn!` block (perhaps not saved yet).
fn crate_for(path: &Path, text: Option<&str>) -> Option<Config> {
    let mut dir = path.parent()?.to_path_buf();
    loop {
        let m = dir.join("Cargo.toml");
        if m.exists() {
            if let Ok(cfg) = load_config(&m) {
                if cfg.is_spec(path) {
                    return Some(cfg);
                }
                let here = path.canonicalize().unwrap_or(path.to_path_buf());
                let src = cfg.crate_dir.join("src");
                let scanned = cfg.spec_manual.is_none() && here.starts_with(&src) && !here.starts_with(src.join("bin"));
                if scanned && text.is_some_and(djinn_syntax::project::has_djinn) {
                    return Some(cfg);
                }
            }
            return None;
        }
        if !dir.pop() {
            return None;
        }
    }
}

/// The specification's texts with the buffer in place of its file (or
/// added, if the file is new to the specification), and the buffer's index.
fn spec_texts_with(cfg: &Config, path: &Path, text: &str) -> (Vec<String>, usize) {
    let here = path.canonicalize().unwrap_or(path.to_path_buf());
    let mut texts = Vec::new();
    let mut idx = None;
    for f in cfg.specs() {
        if f.path.canonicalize().unwrap_or(f.path.clone()) == here {
            idx = Some(texts.len());
            texts.push(text.to_string());
        } else {
            texts.push(std::fs::read_to_string(&f.path).unwrap_or_default());
        }
    }
    let idx = idx.unwrap_or_else(|| {
        texts.push(text.to_string());
        texts.len() - 1
    });
    (texts, idx)
}

fn pos(line1: usize, col0: usize) -> Position {
    Position { line: line1.saturating_sub(1) as u32, character: col0 as u32 }
}

fn line_range(text: &str, line1: usize) -> Range {
    let len = text.lines().nth(line1.saturating_sub(1)).map(|l| l.len()).unwrap_or(0);
    Range { start: pos(line1, 0), end: pos(line1, len) }
}

/// Declarations of a document: (name, kind, 1-based line, 0-based column, name length)
fn decls_of(text: &str) -> Result<Vec<(String, String, usize, usize)>, djinn_syntax::Error> {
    let decls = djinn_syntax::parse_file(text)?;
    Ok(decls
        .into_iter()
        .map(|d| {
            let st = d.name_span.start();
            (d.name.clone(), d.kind.word().into(), st.line, st.column)
        })
        .collect())
}

fn find_theorem_line(file: &Path, decl: &str) -> Option<u32> {
    let text = std::fs::read_to_string(file).ok()?;
    text.lines().position(|l| l.starts_with(&format!("theorem {decl}."))).map(|n| n as u32)
}

// ----------------------------------------------------------------- handlers

fn handle_notification(ctx: &Ctx, n: Notification) {
    match n.method.as_str() {
        "textDocument/didOpen" => {
            let p: DidOpenTextDocumentParams = serde_json::from_value(n.params).unwrap();
            let uri = p.text_document.uri.as_str().to_string();
            ctx.state.lock().unwrap().docs.insert(uri.clone(), Doc { text: p.text_document.text, version: p.text_document.version });
            schedule_lint(ctx, &uri, 0);
        }
        "textDocument/didChange" => {
            let p: DidChangeTextDocumentParams = serde_json::from_value(n.params).unwrap();
            let uri = p.text_document.uri.as_str().to_string();
            if let Some(change) = p.content_changes.into_iter().last() {
                ctx.state.lock().unwrap().docs.insert(uri.clone(), Doc { text: change.text, version: p.text_document.version });
                schedule_lint(ctx, &uri, 600);
            }
        }
        "textDocument/didSave" => {
            let p: DidSaveTextDocumentParams = serde_json::from_value(n.params).unwrap();
            let uri = p.text_document.uri.as_str().to_string();
            if let Some(t) = p.text {
                let mut st = ctx.state.lock().unwrap();
                let v = st.docs.get(&uri).map(|d| d.version).unwrap_or(0);
                st.docs.insert(uri.clone(), Doc { text: t, version: v });
            }
            schedule_lint(ctx, &uri, 0);
        }
        "textDocument/didClose" => {
            let p: DidCloseTextDocumentParams = serde_json::from_value(n.params).unwrap();
            let uri = p.text_document.uri.as_str().to_string();
            ctx.state.lock().unwrap().docs.remove(&uri);
            ctx.notify::<notification::PublishDiagnostics>(PublishDiagnosticsParams { uri: p.text_document.uri, diagnostics: vec![], version: None });
        }
        _ => {}
    }
}

fn handle_request(ctx: &Ctx, req: Request) {
    let id = req.id.clone();
    let result: Result<Value, String> = match req.method.as_str() {
        "textDocument/codeLens" => {
            let p: CodeLensParams = serde_json::from_value(req.params).unwrap();
            Ok(serde_json::to_value(code_lenses(ctx, &p.text_document.uri)).unwrap())
        }
        "textDocument/inlayHint" => {
            let p: InlayHintParams = serde_json::from_value(req.params).unwrap();
            Ok(serde_json::to_value(inlay_hints(ctx, &p.text_document.uri)).unwrap())
        }
        "workspace/executeCommand" => {
            let p: ExecuteCommandParams = serde_json::from_value(req.params).unwrap();
            execute(ctx, &p.command, &p.arguments).map(|_| Value::Null)
        }
        _ => Err(format!("unsupported method {}", req.method)),
    };
    let resp = match result {
        Ok(v) => Response::new_ok(id, v),
        Err(e) => Response::new_err(id, lsp_server::ErrorCode::InvalidRequest as i32, e),
    };
    let _ = ctx.sender.send(Message::Response(resp));
}

// ------------------------------------------------------------------- status

/// Per-declaration status line and detail, from the last verify report.
fn status_views(cfg: &Config, path: &Path, text: &str) -> HashMap<String, (String, String)> {
    let report = verify::Report::load(cfg);
    let (texts, _) = spec_texts_with(cfg, path, text);
    let views = status::views_text(cfg, report.as_ref(), None, &texts);
    // the files on disk against the report's fingerprint, as the build gate
    // checks them: a mismatch makes every verdict of the report stale
    let stale = report.as_ref().and_then(|r| status::evidence_check(cfg, r).message());
    let mut m = HashMap::new();
    for v in views {
        let proved = v.obs.iter().filter(|(_, s)| *s == ObState::Verified).count();
        let short = if v.changed {
            "changed since verification".to_string()
        } else if let Some(why) = &stale {
            why.clone()
        } else if v.kind == "rel" {
            // a rel has no implementation: only proof obligations, if any
            if v.obs.is_empty() {
                "✓ nothing to prove".to_string()
            } else if v.all_verified() {
                "✓ ok".to_string()
            } else {
                format!("{}/{} proved", proved, v.obs.len())
            }
        } else {
            let un = v.get("unambiguous");
            let ic = v.get("impl_correct");
            if v.implemented && v.all_verified() {
                "✓ ok".into()
            } else if un != ObState::Verified {
                "unambiguity unproved".into()
            } else if !v.implemented {
                "unambiguous · no implementation".into()
            } else if ic == ObState::Verified {
                "impl ✓".into()
            } else {
                "impl drafted · correctness unproved".into()
            }
        };
        let detail = v.line().trim().to_string();
        m.insert(v.name.clone(), (short, detail));
    }
    m
}

/// The smoke-test verdict for a declaration, with its first counterexample.
fn smoke_summary(report: Option<&SmokeReport>, name: &str) -> Option<String> {
    let r = report?;
    let d = r.decls.iter().find(|d| d.name == name)?;
    let mut parts = Vec::new();
    for c in &d.checks {
        if let CheckStatus::Problem { what, examples, conflicts, example_input, .. } = &c.status {
            let mut p = what.to_lowercase();
            let ex = examples.first().map(|e| e.trim_start_matches("counterexample: ").to_string()).or_else(|| {
                if conflicts.is_empty() {
                    None
                } else {
                    let lines: Vec<String> = conflicts.iter().map(|(l, t)| format!("line {l}: {t}")).collect();
                    Some(format!("{}{}", lines.join(" vs "), example_input.as_ref().map(|e| format!(" (at {e})")).unwrap_or_default()))
                }
            });
            if let Some(e) = ex {
                let compact: String = e.split_whitespace().collect::<Vec<_>>().join(" ");
                let short: String = compact.chars().take(90).collect();
                p.push_str(&format!(" — {short}{}", if compact.chars().count() > 90 { "…" } else { "" }));
            }
            parts.push(p);
        }
    }
    if parts.is_empty() && d.checks.iter().all(|c| matches!(c.status, CheckStatus::Skipped)) {
        return Some("smoke skipped".into());
    }
    Some(if parts.is_empty() { "smoke ok".into() } else { format!("smoke: {}", parts.join("; ")) })
}

/// One label per declaration, shared by the code lens and the inlay hint so
/// the two can never disagree: (short label, full detail for tooltips).
fn status_label(views: &HashMap<String, (String, String)>, smoke: Option<&SmokeReport>, name: &str) -> (String, String) {
    let (short, detail) = views.get(name).cloned().unwrap_or(("unverified".into(), String::new()));
    let mut label = short.clone();
    match smoke_summary(smoke, name) {
        Some(s) if s == "smoke ok" => {
            if !short.starts_with('✓') {
                label.push_str(" · smoke ok");
            }
        }
        Some(s) => label.push_str(&format!(" · {s}")),
        None => {}
    }
    (label, detail)
}

fn code_lenses(ctx: &Ctx, uri: &Uri) -> Vec<CodeLens> {
    let path = uri_to_path(uri);
    let st = ctx.state.lock().unwrap();
    let Some(doc) = st.docs.get(uri.as_str()) else { return vec![] };
    let Some(cfg) = crate_for(&path, Some(&doc.text)) else { return vec![] };
    let Ok(decls) = decls_of(&doc.text) else { return vec![] };
    let views = status_views(&cfg, &path, &doc.text);
    let smoke = st.smoke.get(uri.as_str());
    let mut out = Vec::new();
    for (i, (name, _kind, line, col)) in decls.iter().enumerate() {
        let range = Range { start: pos(*line, *col), end: pos(*line, col + name.len()) };
        let (label, detail) = status_label(&views, smoke, name);
        let title = format!("djinn: {label}");
        let cmd = |title: String, command: &str, args: Vec<Value>| Command { title, command: command.into(), arguments: Some(args) };
        let a = vec![json!(uri.as_str()), json!(name)];
        out.push(CodeLens { range, command: Some(cmd(title, "djinn.openObligations", a.clone())), data: Some(json!(detail)) });
        out.push(CodeLens { range, command: Some(cmd("proofs".into(), "djinn.openProofs", a.clone())), data: None });
        if i == 0 {
            out.push(CodeLens { range, command: Some(cmd("▶ implement".into(), "djinn.implement", vec![json!(uri.as_str())])), data: None });
            out.push(CodeLens { range, command: Some(cmd("verify".into(), "djinn.verify", vec![json!(uri.as_str())])), data: None });
            out.push(CodeLens { range, command: Some(cmd("smoke-test".into(), "djinn.smokeTest", vec![json!(uri.as_str())])), data: None });
            out.push(CodeLens { range, command: Some(cmd("guide".into(), "djinn.openGuide", vec![json!(uri.as_str())])), data: None });
        }
    }
    out
}

fn inlay_hints(ctx: &Ctx, uri: &Uri) -> Vec<InlayHint> {
    let path = uri_to_path(uri);
    let st = ctx.state.lock().unwrap();
    let Some(doc) = st.docs.get(uri.as_str()) else { return vec![] };
    let Some(cfg) = crate_for(&path, Some(&doc.text)) else { return vec![] };
    let Ok(decls) = decls_of(&doc.text) else { return vec![] };
    let views = status_views(&cfg, &path, &doc.text);
    let smoke = st.smoke.get(uri.as_str());
    let mut out = Vec::new();
    for (name, _kind, line, _col) in &decls {
        let end = line_range(&doc.text, *line).end;
        let (label, detail) = status_label(&views, smoke, name);
        out.push(InlayHint {
            position: end,
            label: InlayHintLabel::String(format!("⟵ {label}")),
            kind: None,
            text_edits: None,
            tooltip: if detail.is_empty() { None } else { Some(InlayHintTooltip::String(detail)) },
            padding_left: Some(true),
            padding_right: None,
            data: None,
        });
    }
    out
}

// --------------------------------------------------------------------- lint

fn schedule_lint(ctx: &Ctx, uri: &str, delay_ms: u64) {
    let gen = {
        let mut st = ctx.state.lock().unwrap();
        let g = st.gen.entry(uri.to_string()).or_insert(0);
        *g += 1;
        *g
    };
    let ctx = ctx.clone();
    let uri = uri.to_string();
    std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_millis(delay_ms));
        let (text, version) = {
            let st = ctx.state.lock().unwrap();
            if st.gen.get(&uri).copied() != Some(gen) {
                return;
            }
            match st.docs.get(&uri) {
                Some(d) => (d.text.clone(), d.version),
                None => return,
            }
        };
        let Ok(u) = Uri::from_str(&uri) else { return };
        let path = uri_to_path(&u);
        let Some(cfg) = crate_for(&path, Some(&text)) else { return };
        let diags = lint(&ctx, &cfg, &uri, &text);
        if ctx.state.lock().unwrap().gen.get(&uri).copied() != Some(gen) {
            return;
        }
        ctx.notify::<notification::PublishDiagnostics>(PublishDiagnosticsParams { uri: u, diagnostics: diags, version: Some(version) });
        ctx.refresh();
    });
}

fn lint(ctx: &Ctx, cfg: &Config, uri: &str, text: &str) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    // syntax and scoping first
    if let Err(e) = djinn_syntax::parse_file(text) {
        let s = e.span.start();
        diags.push(Diagnostic {
            range: Range { start: pos(s.line, s.column), end: pos(s.line, s.column + 1) },
            severity: Some(DiagnosticSeverity::ERROR),
            source: Some("djinn".into()),
            message: e.msg,
            ..Default::default()
        });
        ctx.state.lock().unwrap().smoke.remove(uri);
        return diags;
    }
    let bounds = smoke::Bounds { timeout_ms: 5_000, ..Default::default() };
    // the whole specification, for what this file uses from the others;
    // findings of this file only
    let (texts, me) = spec_texts_with(cfg, &uri_to_path(&match Uri::from_str(uri) {
        Ok(u) => u,
        Err(_) => return diags,
    }), text);
    let mut report = match smoke::smoke_run_sources(&texts, &bounds) {
        Ok(r) => r,
        Err((_, e)) => {
            ctx.log(format!("smoke-test failed: {e}"));
            return diags;
        }
    };
    report.decls.retain(|d| d.file == me);
    let Ok(u) = Uri::from_str(uri) else { return diags };
    for d in &report.decls {
        let name_range = Range { start: pos(d.line, d.col - 1), end: pos(d.line, d.col - 1 + d.name.len()) };
        for c in &d.checks {
            if let CheckStatus::Problem { what, how_many, examples, conflict_title, conflicts, example_input } = &c.status {
                let severity = if what.starts_with("ENSURES") { DiagnosticSeverity::WARNING } else { DiagnosticSeverity::ERROR };
                let mut message = format!("{} {}: {what} — {how_many}", d.name, c.label);
                for e in examples.iter().take(2) {
                    message.push_str(&format!("\n{e}"));
                }
                if let Some(e) = example_input {
                    message.push_str(&format!("\ne.g. at {e}"));
                }
                if !conflicts.is_empty() {
                    message.push_str(&format!("\n{conflict_title}"));
                    for (line, t) in conflicts {
                        message.push_str(&format!("\n  line {line}: {t}"));
                    }
                }
                let related: Vec<DiagnosticRelatedInformation> = conflicts
                    .iter()
                    .map(|(line, t)| DiagnosticRelatedInformation {
                        location: Location { uri: u.clone(), range: line_range(text, *line) },
                        message: format!("part of the conflict: {t}"),
                    })
                    .collect();
                diags.push(Diagnostic {
                    range: name_range,
                    severity: Some(severity),
                    source: Some("djinn smoke-test".into()),
                    code: Some(NumberOrString::String(c.label.replace(' ', "-"))),
                    message,
                    related_information: if related.is_empty() { None } else { Some(related) },
                    ..Default::default()
                });
                // also mark each conflicting statement, with a short self-contained message
                let at = example_input.as_ref().map(|e| format!(" at {e}")).unwrap_or_default();
                for (line, t) in conflicts {
                    let message = if conflicts.len() == 1 {
                        if what.starts_with("NO OUTPUT") {
                            format!("{}: no output satisfies this statement{at}", d.name)
                        } else {
                            format!("{}: this statement is unsatisfiable{at}", d.name)
                        }
                    } else {
                        let others: Vec<String> = conflicts.iter().filter(|(l, _)| l != line).map(|(l, ot)| format!("line {l} ({})", ot.trim_end_matches(';'))).collect();
                        format!("{}: contradicts {}{at}", d.name, others.join(" and "))
                    };
                    let _ = t;
                    diags.push(Diagnostic {
                        range: line_range(text, *line),
                        severity: Some(DiagnosticSeverity::ERROR),
                        source: Some("djinn smoke-test".into()),
                        message,
                        ..Default::default()
                    });
                }
            }
        }
    }
    ctx.state.lock().unwrap().smoke.insert(uri.to_string(), report);
    diags
}

// ----------------------------------------------------------------- commands

fn arg_uri(args: &[Value], i: usize) -> Result<Uri, String> {
    let s = args.get(i).and_then(|v| v.as_str()).ok_or("missing document argument")?;
    Uri::from_str(s).map_err(|e| format!("bad uri: {e}"))
}

fn execute(ctx: &Ctx, command: &str, args: &[Value]) -> Result<(), String> {
    let uri = arg_uri(args, 0)?;
    let path = uri_to_path(&uri);
    let text = ctx.state.lock().unwrap().docs.get(uri.as_str()).map(|d| d.text.clone());
    let cfg = crate_for(&path, text.as_deref()).ok_or("this file is not a specification file of a Djinn crate")?;
    match command {
        "djinn.openObligations" | "djinn.openProofs" | "djinn.openGuide" => {
            let file = match command {
                "djinn.openObligations" => cfg.lean_dir().join("Obligations.lean"),
                "djinn.openProofs" => cfg.lean_dir().join("Proofs.lean"),
                _ => cfg.guide_path(),
            };
            if !file.exists() {
                // produce the trusted files first
                if let Err(e) = verify::translate(&cfg, &mut verify::Log::new(false)) {
                    return Err(format!("translate failed: {e}"));
                }
            }
            let name = args.get(1).and_then(|v| v.as_str()).unwrap_or("");
            let line = if name.is_empty() { None } else { find_theorem_line(&file, name) };
            let target = path_to_uri(&file).ok_or("bad path")?;
            let selection = line.map(|l| Range { start: Position { line: l, character: 0 }, end: Position { line: l, character: 0 } });
            let _ = ctx.request::<request::ShowDocument>(ShowDocumentParams { uri: target, external: Some(false), take_focus: Some(true), selection });
            Ok(())
        }
        "djinn.smokeTest" => {
            let text = text.unwrap_or_default();
            let ctx2 = ctx.clone();
            let cfg2 = cfg.clone();
            let u = uri.as_str().to_string();
            std::thread::spawn(move || {
                let diags = lint(&ctx2, &cfg2, &u, &text);
                let problems = diags.len();
                if let Ok(uu) = Uri::from_str(&u) {
                    ctx2.notify::<notification::PublishDiagnostics>(PublishDiagnosticsParams { uri: uu, diagnostics: diags, version: None });
                }
                ctx2.refresh();
                ctx2.show(if problems == 0 { MessageType::INFO } else { MessageType::WARNING }, if problems == 0 { "smoke-test: no contradiction and no counterexample within the bounds".to_string() } else { format!("smoke-test: {problems} finding(s); see the diagnostics") });
            });
            Ok(())
        }
        "djinn.status" => {
            let text = status::status_text(&cfg);
            ctx.log(text.clone());
            ctx.show(MessageType::INFO, text.lines().take(8).collect::<Vec<_>>().join("\n"));
            Ok(())
        }
        "djinn.implement" | "djinn.verify" => {
            let agent = args.get(1).and_then(|v| v.as_str()).unwrap_or("codex").to_string();
            let manifest = cfg.crate_dir.join("Cargo.toml");
            let bin = ctx.bin.clone();
            let ctx2 = ctx.clone();
            let is_impl = command == "djinn.implement";
            std::thread::spawn(move || run_driver(&ctx2, &bin, &manifest, is_impl, &agent));
            Ok(())
        }
        _ => Err(format!("unknown command {command}")),
    }
}

/// Run `cargo-djinn implement|verify` as a child, streaming its progress.
fn run_driver(ctx: &Ctx, bin: &Path, manifest: &Path, is_impl: bool, agent: &str) {
    use std::io::BufRead;
    let token = NumberOrString::String(format!("djinn-{}", ctx.ids.fetch_add(1, Ordering::SeqCst)));
    let _ = ctx.request::<request::WorkDoneProgressCreate>(WorkDoneProgressCreateParams { token: token.clone() });
    let title = if is_impl { format!("djinn implement ({agent})") } else { "djinn verify".to_string() };
    ctx.notify::<notification::Progress>(ProgressParams {
        token: token.clone(),
        value: ProgressParamsValue::WorkDone(WorkDoneProgress::Begin(WorkDoneProgressBegin { title: title.clone(), cancellable: Some(false), message: Some("starting".into()), percentage: None })),
    });
    let mut cmd = std::process::Command::new(bin);
    if is_impl {
        cmd.args(["implement", "--agent", agent]);
    } else {
        cmd.arg("verify");
    }
    cmd.arg("--manifest-path").arg(manifest);
    cmd.stdout(std::process::Stdio::piped()).stderr(std::process::Stdio::piped()).stdin(std::process::Stdio::null());
    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            ctx.show(MessageType::ERROR, format!("cannot run {}: {e}", bin.display()));
            return;
        }
    };
    let stderr = child.stderr.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let ctx_out = ctx.clone();
    let out_thread = std::thread::spawn(move || {
        let mut last = String::new();
        for line in std::io::BufReader::new(stdout).lines().flatten() {
            ctx_out.log(line.clone());
            last = line;
        }
        last
    });
    let mut last_lines: Vec<String> = Vec::new();
    let mut last_refresh = std::time::Instant::now();
    for line in std::io::BufReader::new(stderr).lines().flatten() {
        ctx.log(line.clone());
        let msg: String = line.trim().chars().take(100).collect();
        ctx.notify::<notification::Progress>(ProgressParams {
            token: token.clone(),
            value: ProgressParamsValue::WorkDone(WorkDoneProgress::Report(WorkDoneProgressReport { cancellable: Some(false), message: Some(msg), percentage: None })),
        });
        // keep the editor's status current while the agent works: every
        // verify writes the report, and the monitor announces it
        if line.contains("verify #") || line.contains(": → ") || last_refresh.elapsed().as_secs() >= 10 {
            ctx.refresh();
            last_refresh = std::time::Instant::now();
        }
        last_lines.push(line);
        if last_lines.len() > 12 {
            last_lines.remove(0);
        }
    }
    let status = child.wait().ok();
    let last_out = out_thread.join().unwrap_or_default();
    // exit 3: every obligation proved while some `fn` has no implementation
    // (spec only): named from the report as verify prints it, like a PASS
    let ok = status.map(|s| s.success() || s.code() == Some(3)).unwrap_or(false);
    let verdict = if ok { load_config(manifest).ok().and_then(|cfg| verify::Report::load(&cfg)).map(|r| status::verdict(&r)).unwrap_or_else(|| "PASS".into()) } else { "FAIL".into() };
    ctx.notify::<notification::Progress>(ProgressParams {
        token: token.clone(),
        value: ProgressParamsValue::WorkDone(WorkDoneProgress::End(WorkDoneProgressEnd { message: Some(verdict.clone()) })),
    });
    let _ = last_out;
    // one line for the message area; the details are in the log
    let fail_line = last_lines.iter().rev().find(|l| l.starts_with("FAIL")).cloned().unwrap_or_else(|| last_lines.last().cloned().unwrap_or_default());
    ctx.show(if ok { MessageType::INFO } else { MessageType::WARNING }, format!("{title}: {}", if verdict == "PASS" { "PASS — every obligation verified".to_string() } else if ok { verdict } else { fail_line }));
    ctx.refresh();
}
