//! Every module has a row in `docs/modules.md` (architecture §8): a new
//! file without its contract object, reuse, reason and end-to-end test is a
//! second calculator, not part of the kernel.

use std::collections::BTreeSet;
use std::fs;

fn rust_files(dir: &str) -> BTreeSet<String> {
    fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .filter(|n| n.ends_with(".rs"))
        .map(|n| format!("{dir}/{n}"))
        .collect()
}

#[test]
fn every_module_is_registered() {
    let registry = fs::read_to_string("docs/modules.md").unwrap();
    let rows: BTreeSet<String> = registry
        .lines()
        .filter_map(|l| l.strip_prefix("| `"))
        .filter_map(|l| l.split('`').next())
        .map(str::to_string)
        .collect();
    let files: BTreeSet<String> = rust_files("src")
        .union(&rust_files("examples"))
        .cloned()
        .collect();
    let missing: Vec<_> = files.difference(&rows).collect();
    let stale: Vec<_> = rows.difference(&files).collect();
    assert!(
        missing.is_empty(),
        "modules without a row in docs/modules.md (architecture §8): {missing:?}"
    );
    assert!(
        stale.is_empty(),
        "rows in docs/modules.md without a file: {stale:?}"
    );
}
