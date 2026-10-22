//! `cargo djinn` — the Djinn-on-Aeneas driver.
//!
//! translate            emit the trusted Lean files and the harness guide
//! verify [--jail DIR]  the whole gate; exit 0 iff PASS, 3 if only the specification
//!                      is verified (some `fn` not implemented yet), 1 otherwise
//! implement [opts]     run Claude Code or Codex in a jail against the verifier
//! status               declarations implemented/proved, agent jobs, cost
//! clean                archive solution + proofs in .djinnscratch/backup/, remove the derived files
//! clean --restore [ID] bring a backup (from `clean` or `-B`) back and verify it
//! guide                print GUIDE.md
//! mcp --jail DIR       the MCP server the agents call (internal)

use cargo_djinn::config::load_config;
use cargo_djinn::{agent, bench, guide, mcp, optimize, smoke, status, verify};
use std::path::PathBuf;
use std::process::ExitCode;

/// `verify`'s exit status when only the specification is verified.
const SPEC_ONLY: u8 = 3;

fn usage() -> ExitCode {
    eprintln!(
        "usage: cargo djinn <command> [--manifest-path Cargo.toml]
  translate
  verify [--jail DIR]                          exit status: 0 PASS, 1 FAIL, 3 specification verified
                                               but some fn not implemented yet (not a PASS)
  implement [--agent codex|claude] [--background] [-B|--reimplement] [--yolo] [--model M] [--effort E]
            [--limit USD] [--max-budget-usd N] [--args \"...\"] [--prompt TEXT | --prompt-file F]
            (reuses existing solution/proofs and only completes what is missing; -B starts over)
  status
  clean                                        archive solution and proofs in .djinnscratch/backup/<time>/, remove derived files
  clean --restore [ID]                         bring a backup back (the latest, or ID from --list) and verify it
  clean --list                                 the backups and what they hold
  guide
  bench [--min-time S] [--batches K] [--jobs J] time the workload named by [package.metadata.djinn] bench
                                               (with bench_points: every point, J at a time; default 4)
  optimize (--cycles N | --limit USD) [--min-time S] [--batches K] [--jobs J] [--threshold PCT]
           [--agent codex|claude] [--model M] [--args \"...\"] [--prompt TEXT]
           (hill-climb on the workload under the verifier; Ctrl-C reverts to the last known-good state;
            a restart resumes the history: --cycles and --limit count every run; exit 5 on an agent API error)
  smoke-test [--max-len N] [--int-bound B] [--max-examples K] [--timeout S] [--only NAME]
            (bounded symbolic checks of the spec with Z3; never run by other commands)"
    );
    ExitCode::from(2)
}

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    if args.first().map(|s| s == "djinn").unwrap_or(false) {
        args.remove(0);
    }
    let bin = std::env::current_exe().unwrap_or_else(|_| PathBuf::from("cargo-djinn"));
    let mut manifest = PathBuf::from("Cargo.toml");
    let mut cmd: Option<String> = None;
    let mut jail: Option<PathBuf> = None;
    let mut opts = agent::Opts {
        agent: agent::Agent::Codex,
        model: None,
        yolo: false,
        background: false,
        extra_prompt: None,
        max_budget_usd: None,
        effort: None,
        extra_args: Vec::new(),
        limit_usd: None,
        from_scratch: false,
    };
    let mut job_id: Option<String> = None;
    let mut sb = smoke::Bounds::default();
    let mut cycles: Option<usize> = None;
    let mut min_time = 5.0f64;
    let mut batches = 5usize;
    let mut jobs = 4usize;
    let mut threshold = 0.03f64;
    let mut bench_override: Option<String> = None;
    let mut restore: Option<Option<String>> = None;
    let mut list_backups = false;
    let mut i = 0;
    let next = |i: &mut usize, args: &[String]| -> Result<String, ExitCode> {
        *i += 1;
        args.get(*i).cloned().ok_or_else(usage)
    };
    while i < args.len() {
        match args[i].as_str() {
            "--manifest-path" => manifest = PathBuf::from(match next(&mut i, &args) { Ok(v) => v, Err(c) => return c }),
            "--jail" => jail = Some(PathBuf::from(match next(&mut i, &args) { Ok(v) => v, Err(c) => return c })),
            "--restore" => {
                // an optional backup id (`20261004-235130`) may follow
                let id = args.get(i + 1).filter(|a| a.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false)).cloned();
                if id.is_some() {
                    i += 1;
                }
                restore = Some(id);
            }
            "--list" => list_backups = true,
            "--agent" => {
                opts.agent = match next(&mut i, &args).as_deref() {
                    Ok("claude") => agent::Agent::Claude,
                    Ok("codex") => agent::Agent::Codex,
                    _ => return usage(),
                }
            }
            "--background" | "--bg" => opts.background = true,
            "-B" | "--from-scratch" | "--reimplement" => opts.from_scratch = true,
            "--yolo" => opts.yolo = true,
            "--model" => opts.model = Some(match next(&mut i, &args) { Ok(v) => v, Err(c) => return c }),
            "--effort" => opts.effort = Some(match next(&mut i, &args) { Ok(v) => v, Err(c) => return c }),
            "--max-budget-usd" => opts.max_budget_usd = Some(match next(&mut i, &args) { Ok(v) => v, Err(c) => return c }),
            "--prompt" => opts.extra_prompt = Some(match next(&mut i, &args) { Ok(v) => v, Err(c) => return c }),
            "--args" => opts.extra_args.extend(agent::shell_words(&match next(&mut i, &args) { Ok(v) => v, Err(c) => return c })),
            "--limit" => {
                let v = match next(&mut i, &args) { Ok(v) => v, Err(c) => return c };
                match v.trim_start_matches('$').parse::<f64>() {
                    Ok(l) => opts.limit_usd = Some(l),
                    Err(_) => {
                        eprintln!("--limit expects a USD amount, e.g. --limit 5");
                        return ExitCode::from(2);
                    }
                }
            }
            "--job" => job_id = Some(match next(&mut i, &args) { Ok(v) => v, Err(c) => return c }),
            "--max-len" => sb.max_len = match next(&mut i, &args) { Ok(v) => v.parse().unwrap_or(4), Err(c) => return c },
            "--int-bound" => sb.int_bound = match next(&mut i, &args) { Ok(v) => v.parse().unwrap_or(8), Err(c) => return c },
            "--max-examples" => sb.max_examples = match next(&mut i, &args) { Ok(v) => v.parse().unwrap_or(20), Err(c) => return c },
            "--timeout" => sb.timeout_ms = match next(&mut i, &args) { Ok(v) => v.parse::<u64>().unwrap_or(10) * 1000, Err(c) => return c },
            "--only" => sb.only = Some(match next(&mut i, &args) { Ok(v) => v, Err(c) => return c }),
            "--cycles" => cycles = match next(&mut i, &args) { Ok(v) => v.parse().ok(), Err(c) => return c },
            "--min-time" => min_time = match next(&mut i, &args) { Ok(v) => v.parse().unwrap_or(5.0), Err(c) => return c },
            "--batches" => batches = match next(&mut i, &args) { Ok(v) => v.parse().unwrap_or(5), Err(c) => return c },
            "--jobs" => jobs = match next(&mut i, &args) { Ok(v) => v.parse().unwrap_or(4), Err(c) => return c },
            "--threshold" => threshold = match next(&mut i, &args) { Ok(v) => v.trim_end_matches('%').parse::<f64>().map(|x| x / 100.0).unwrap_or(0.03), Err(c) => return c },
            "--bench" => bench_override = Some(match next(&mut i, &args) { Ok(v) => v, Err(c) => return c }),
            "--prompt-file" => {
                let f = match next(&mut i, &args) { Ok(v) => v, Err(c) => return c };
                match std::fs::read_to_string(&f) {
                    Ok(t) => opts.extra_prompt = Some(t),
                    Err(e) => {
                        eprintln!("{f}: {e}");
                        return ExitCode::from(2);
                    }
                }
            }
            c if cmd.is_none() && !c.starts_with('-') => cmd = Some(c.to_string()),
            _ => return usage(),
        }
        i += 1;
    }
    let mut cfg = match load_config(&manifest) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };
    if let Some(b) = bench_override {
        cfg.bench = Some(b);
    }
    let r: Result<bool, String> = match cmd.as_deref() {
        Some("translate") => verify::translate(&cfg, &mut verify::Log::new(true)).map(|_| true),
        Some("clean") if list_backups => agent::list_backups(&cfg).map(|_| true),
        Some("clean") => match restore {
            Some(id) => match agent::restore(&cfg, id.as_deref()) {
                // the restored work verifies, but some `fn` is unimplemented (as for verify)
                Ok(true) if verify::Report::load(&cfg).is_some_and(|r| !r.unimplemented().is_empty()) => return ExitCode::from(SPEC_ONLY),
                r => r,
            },
            None => agent::clean(&cfg).map(|_| true),
        },
        Some("verify") => {
            let report = verify::verify(&cfg, jail.as_deref(), &mut verify::Log::new(true));
            // every obligation so far proved, but not every `fn` implemented:
            // not a PASS (the build gate refuses the crate), and not a FAIL
            if report.pass && !report.unimplemented().is_empty() {
                return ExitCode::from(SPEC_ONLY);
            }
            Ok(report.pass)
        }
        Some("implement") => agent::implement(&cfg, opts, &bin),
        Some("status") => {
            print!("{}", status::status_text(&cfg));
            Ok(true)
        }
        Some("guide") => match verify::lower_spec(&cfg) {
            Ok(l) => {
                print!("{}", guide::guide(&cfg, &l, &verify::impl_names(&cfg)));
                Ok(true)
            }
            Err(e) => Err(e),
        },
        Some("supervise") => match job_id.and_then(|id| status::load_jobs(&cfg).into_iter().find(|j| j.id == id)) {
            Some(job) => {
                agent::supervise(&job, None);
                Ok(true)
            }
            None => Err("supervise needs --job ID".into()),
        },
        Some("smoke-test") => match smoke::smoke_test(&cfg, &sb) {
            Ok(code) => return ExitCode::from(code),
            Err(e) => Err(e),
        },
        Some("bench") => {
            let mut say = |s: &str| eprintln!("{s}");
            bench::measure(&cfg, min_time, batches, jobs, &mut say).map(|m| {
                println!("{}", m.line());
                if m.is_multi() {
                    print!("{}", m.table());
                }
                true
            })
        }
        Some("optimize") => match optimize::optimize(&cfg, optimize::OptOpts { cycles, min_time, batches, jobs, threshold, agent: opts }, &bin) {
            Ok(code) => return ExitCode::from(code),
            Err(e) => Err(e),
        },
        Some("mcp") => match jail {
            Some(j) => {
                mcp::serve(&cfg, &j);
                Ok(true)
            }
            None => Err("mcp needs --jail DIR".into()),
        },
        _ => return usage(),
    };
    match r {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(1),
        Err(e) => {
            eprintln!("{e}");
            ExitCode::from(1)
        }
    }
}
