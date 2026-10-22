//! A minimal MCP server (stdio, JSON-RPC 2.0) exposing the verifier and the
//! status report as tools. Started by the agent from the jail's `.mcp.json`.

use crate::config::Config;
use crate::verify::{self, Log};
use serde_json::{json, Value};
use std::io::{BufRead, Write};
use std::path::Path;

fn tools() -> Value {
    json!([
        {
            "name": "verify",
            "description": "Run the Djinn verifier on your current solution and proofs: syncs the solution directory and Proofs.lean from this jail into the real crate, then cargo build → charon → aeneas → regenerate trusted Lean → lake build → axiom audit. Returns PASS or the failing stage with the errors. Also refreshes the generated files in the jail (Code/, Spec.lean, Obligations.lean). Takes 10 s to a few minutes.",
            "inputSchema": { "type": "object", "properties": {}, "additionalProperties": false },
            "annotations": { "readOnlyHint": true, "destructiveHint": false, "openWorldHint": false }
        },
        {
            "name": "status",
            "description": "Per-declaration progress: which funcs are implemented, which obligations are proved, from the last verify run.",
            "inputSchema": { "type": "object", "properties": {}, "additionalProperties": false },
            "annotations": { "readOnlyHint": true, "destructiveHint": false, "openWorldHint": false }
        }
    ])
}

pub fn serve(cfg: &Config, jail: &Path) {
    let stdin = std::io::stdin();
    let mut out = std::io::stdout();
    let reply = |out: &mut std::io::Stdout, id: Value, result: Value| {
        let msg = json!({ "jsonrpc": "2.0", "id": id, "result": result });
        let _ = writeln!(out, "{}", msg);
        let _ = out.flush();
    };
    let error = |out: &mut std::io::Stdout, id: Value, code: i64, msg: &str| {
        let m = json!({ "jsonrpc": "2.0", "id": id, "error": { "code": code, "message": msg } });
        let _ = writeln!(out, "{}", m);
        let _ = out.flush();
    };
    for line in stdin.lock().lines() {
        let Ok(line) = line else { break };
        if line.trim().is_empty() {
            continue;
        }
        let Ok(req) = serde_json::from_str::<Value>(&line) else { continue };
        let method = req["method"].as_str().unwrap_or("").to_string();
        let id = req.get("id").cloned().unwrap_or(Value::Null);
        if id.is_null() {
            continue; // a notification
        }
        match method.as_str() {
            "initialize" => {
                let pv = req["params"]["protocolVersion"].as_str().unwrap_or("2024-11-05").to_string();
                reply(
                    &mut out,
                    id,
                    json!({
                        "protocolVersion": pv,
                        "capabilities": { "tools": {} },
                        "serverInfo": { "name": "djinn", "version": env!("CARGO_PKG_VERSION") }
                    }),
                );
            }
            "ping" => reply(&mut out, id, json!({})),
            "tools/list" => reply(&mut out, id, json!({ "tools": tools() })),
            "tools/call" => {
                let name = req["params"]["name"].as_str().unwrap_or("");
                let (text, is_error) = match name {
                    "verify" => {
                        let mut log = Log::new(false);
                        let report = verify::verify(cfg, Some(jail), &mut log);
                        let tail: Vec<&str> = log.text.lines().rev().take(120).collect::<Vec<_>>().into_iter().rev().collect();
                        // a specification-only PASS (some `fn` not implemented) is no pass
                        (format!("{}\n--- verifier output (tail) ---\n{}", report.summary(), tail.join("\n")), !report.pass || !report.unimplemented().is_empty())
                    }
                    "status" => (crate::status::status_text(cfg), false),
                    _ => (format!("unknown tool `{name}`"), true),
                };
                reply(&mut out, id, json!({ "content": [{ "type": "text", "text": text }], "isError": is_error }));
            }
            _ => error(&mut out, id, -32601, "method not found"),
        }
    }
}
