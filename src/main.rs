use std::process::ExitCode;

use agl::model::plane_to_string;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let verbose = args.iter().any(|a| a == "-v");
    let diagnose = args.iter().any(|a| a == "--diagnose");
    let propose = args.iter().any(|a| a == "--propose");
    let concepts = args.iter().any(|a| a == "--concepts");
    let learn = args
        .iter()
        .position(|a| a == "--learn")
        .and_then(|i| args.get(i + 1).cloned());
    let implications = args.iter().any(|a| a == "--implications");
    let explore = args.iter().any(|a| a == "--explore");
    let hidden = args.iter().any(|a| a == "--scale");
    let layer = args.iter().any(|a| a == "--layer");
    let where_ = args
        .iter()
        .position(|a| a == "--where")
        .and_then(|i| args.get(i + 1).cloned());
    let takes_value = |i: usize| i > 0 && (args[i - 1] == "--learn" || args[i - 1] == "--where");
    let files: Vec<&String> = args
        .iter()
        .enumerate()
        .filter(|(i, a)| !(a.starts_with('-') || takes_value(*i)))
        .map(|(_, a)| a)
        .collect();
    if files.is_empty() {
        eprintln!(
            "usage: agl [-v] [--diagnose] [--propose] [--concepts] [--implications] [--explore] [--scale] [--layer] [--learn REL] [--where ATOM] FILE.agl..."
        );
        return ExitCode::from(2);
    }
    if layer {
        // Each file is one world; the findings go out as a world for the
        // kernel (H75, stage A).
        let mut worlds = Vec::new();
        for path in &files {
            let prog = match agl::parse_file(std::path::Path::new(path)) {
                Ok(p) => p,
                Err(e) => {
                    eprintln!("{path}: parse error: {e}");
                    return ExitCode::FAILURE;
                }
            };
            let (rels, domain, why) = agl::bank::relations(&prog);
            if let Some(why) = why {
                eprintln!("{path}: {why}");
                return ExitCode::FAILURE;
            }
            let exts: Vec<_> = rels.into_iter().map(|(_, e)| e).collect();
            worlds.push((domain.len(), exts));
        }
        print!("{}", agl::layer::to_agl(&agl::layer::explore(&worlds)));
        return ExitCode::SUCCESS;
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
        for e in &report.exceptions {
            println!(
                "exception: {} lost in {} to {}",
                e.atom,
                plane_to_string(&e.context),
                e.by
            );
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
        for c in &report.compares {
            let (status, verdict) = match (&c.verdict, c.compare.expect) {
                (Ok(v), Some(e)) if *v == e => ("PASS", v.to_string()),
                (Ok(v), Some(_)) => ("FAIL", v.to_string()),
                (Ok(v), None) => ("    ", v.to_string()),
                (Err(_), _) => ("FAIL", "error".to_string()),
            };
            let expect = c
                .compare
                .expect
                .map(|e| format!(" (expected {e})"))
                .unwrap_or_default();
            let extent = c
                .extent
                .as_ref()
                .map(|e| format!("; {e}"))
                .unwrap_or_default();
            println!(
                "{status} line {}: {} @ {} vs {} @ {} → {verdict}{expect}{extent}",
                c.compare.line,
                c.compare.left.0,
                plane_to_string(&c.compare.left.1),
                c.compare.right.0,
                plane_to_string(&c.compare.right.1),
            );
            if verbose || status == "FAIL" {
                for l in c.explanation.lines() {
                    println!("       {l}");
                }
            }
        }
        if concepts {
            print!("{}", agl::concept::report(&prog));
        }
        if let Some(src) = &where_ {
            match agl::parse::parse_atom_in(src, &prog.units) {
                Ok(pat) => {
                    let (exts, complete) = agl::extent::extents(&prog, &pat);
                    print!("{}", agl::extent::render_extents(&exts, complete));
                }
                Err(e) => {
                    println!("--where: {e}");
                    ok = false;
                }
            }
        }
        if implications {
            print!(
                "{}",
                agl::extent::render_implications(&agl::extent::implications(&prog))
            );
        }
        if diagnose {
            let ds = agl::reflect::diagnose(&prog);
            if ds.is_empty() {
                println!("diagnosis: nothing to diagnose");
            } else {
                print!("{}", agl::reflect::render(&ds));
            }
        }
        if explore {
            let clean = report
                .diags
                .iter()
                .all(|d| d.level != agl::lint::Level::Error);
            if clean {
                let (rels, domain, why) = agl::bank::relations(&prog);
                if let Some(why) = why {
                    println!("explore: {why}");
                }
                println!("domain: {}", domain.len());
                let banks: Vec<_> = rels
                    .into_iter()
                    .map(|(r, e)| agl::bank::Bank::grow(r, e, true))
                    .collect();
                let kinds = agl::bank::Kinds::build(&banks);
                print!("{}", agl::bank::render(&banks, &kinds, verbose));
            } else {
                println!("explore: fix the errors above first");
            }
        }
        if hidden {
            let (rels, domain, why) = agl::bank::relations(&prog);
            match why {
                Some(why) => println!("scale: {why}"),
                None => print!("{}", agl::scale::render(&rels, &domain)),
            }
        }
        if prog.clean.is_some() && (learn.is_some() || propose) {
            // A template or a menu of operations is given ready-made (H72).
            println!("clean world: --learn and --propose take a hand-given template or menu");
            ok = false;
        } else if let Some(target) = &learn {
            let (hs, notes) = agl::learn::learn(&prog, target);
            print!("{}", agl::learn::render(&hs, &notes));
        }
        if propose && prog.clean.is_none() {
            let (ps, notes) = agl::propose::propose(&prog);
            if ps.is_empty() && notes.is_empty() {
                println!("proposals: none");
            } else {
                print!("{}", agl::propose::render(&ps, &notes));
            }
        }
        if report.has_errors()
            || report.failed_queries().next().is_some()
            || report.failed_compares().next().is_some()
        {
            ok = false;
        }
    }
    if ok {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
