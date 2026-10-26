//! Every module has a row in `docs/modules.md`: a new file without its
//! specification object, reuse, reason and end-to-end test is a second
//! calculator, not part of the kernel.

use std::collections::BTreeSet;
use std::fs;
use std::io::ErrorKind;

/// All `.rs` files under `dir`, recursively, as `dir/sub/file.rs` — the same
/// paths `tools/hooks/guard_module.sh` checks. A missing `dir` is empty.
fn rust_files(dir: &str) -> BTreeSet<String> {
    let entries = match fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(e) if e.kind() == ErrorKind::NotFound => return BTreeSet::new(),
        Err(e) => panic!("{dir}: {e}"),
    };
    let mut files = BTreeSet::new();
    for entry in entries {
        let entry = entry.unwrap();
        let name = entry.file_name().into_string().unwrap();
        let path = format!("{dir}/{name}");
        if entry.file_type().unwrap().is_dir() {
            files.extend(rust_files(&path));
        } else if name.ends_with(".rs") {
            files.insert(path);
        }
    }
    files
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
        "modules without a row in docs/modules.md: {missing:?}"
    );
    assert!(
        stale.is_empty(),
        "rows in docs/modules.md without a file: {stale:?}"
    );
}
