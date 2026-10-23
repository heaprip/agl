//! memote as a differential acceptance test (H38). Each case under
//! `cases/memote/` is the BiGG model e_coli_core or a seeded mutant of it, with
//! memote's own verdicts as expectations; `cases/memote/rules.agl` must
//! reproduce every one of them. Cases are written by `tools/memote_ref.py`.

use std::fs;

#[test]
fn kernel_agrees_with_memote() {
    let mut paths: Vec<_> = fs::read_dir("cases/memote")
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "agl"))
        .filter(|p| p.file_name().is_some_and(|n| n != "rules.agl"))
        .collect();
    paths.sort();
    assert!(paths.len() > 1, "the model and its mutants");
    for path in &paths {
        let prog = agl::parse_file(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        assert!(
            prog.queries.len() > 400,
            "{}: memote's verdicts",
            path.display()
        );
        let report = agl::run(&prog);
        assert!(
            !report.has_errors(),
            "{}: {:?} {:?}",
            path.display(),
            report.diags,
            report.errors
        );
        assert!(
            report.conflicts.is_empty(),
            "{}: {:?}",
            path.display(),
            report.conflicts
        );
        let failed: Vec<_> = report
            .failed_queries()
            .map(|q| format!("line {}: {} -> {}", q.query.line, q.query.atom, q.verdict))
            .collect();
        assert!(failed.is_empty(), "{}: {failed:#?}", path.display());
    }
}
