use std::process::ExitCode;

use agl::model::plane_to_string;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let verbose = args.iter().any(|a| a == "-v");
    let diagnose = args.iter().any(|a| a == "--diagnose");
    let propose = args.iter().any(|a| a == "--propose");
    let files: Vec<&String> = args.iter().filter(|a| !a.starts_with('-')).collect();
    if files.is_empty() {
        eprintln!("usage: agl [-v] [--diagnose] [--propose] FILE.agl...");
        return ExitCode::from(2);
    }
    let mut ok = true;
    for path in files {
        println!("== {path}");
        let prog = match agl::parse_file(std::path::Path::new(path)) {
            Ok(p) => p,
            Err(e) => {
                println!("parse error: {e}");
                ok = false;
                continue;
            }
        };
        let report = agl::run(&prog);
        for d in &report.diags {
            println!("{:?} line {} [{}]: {}", d.level, d.line, d.code, d.msg);
        }
        for e in &report.errors {
            println!("error: {e}");
        }
        for c in &report.conflicts {
            println!(
                "conflict {:?} on {} in {}: for {} / against {}",
                c.conflict.kind,
                c.conflict.positive,
                plane_to_string(&c.context),
                c.conflict.sources_pos.join(", "),
                c.conflict.sources_neg.join(", ")
            );
            if !c.conflict.blame.is_empty() {
                println!("    least trusted: {}", c.conflict.blame.join(", "));
            }
        }
        for r in &report.queries {
            let status = match r.query.expect {
                Some(e) if e == r.verdict => "PASS",
                Some(_) => "FAIL",
                None => "    ",
            };
            let expect = r
                .query
                .expect
                .map(|e| format!(" (expected {e})"))
                .unwrap_or_default();
            let situated = r
                .query
                .situate
                .as_ref()
                .map(|c| format!(" (situate {c})"))
                .unwrap_or_default();
            println!(
                "{status} line {}: {} @ {}{situated} → {}{expect}",
                r.query.line,
                r.query.atom,
                plane_to_string(&r.plane),
                r.verdict
            );
            if verbose || status == "FAIL" {
                for l in r.explanation.lines() {
                    println!("       {l}");
                }
            }
        }
        if diagnose {
            let ds = agl::reflect::diagnose(&prog);
            if ds.is_empty() {
                println!("diagnosis: nothing to diagnose");
            } else {
                print!("{}", agl::reflect::render(&ds));
            }
        }
        if propose {
            let (ps, notes) = agl::propose::propose(&prog);
            if ps.is_empty() && notes.is_empty() {
                println!("proposals: none");
            } else {
                print!("{}", agl::propose::render(&ps, &notes));
            }
        }
        if report.has_errors() || report.failed_queries().next().is_some() {
            ok = false;
        }
    }
    if ok {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
