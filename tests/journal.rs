//! The journal and development from nothing (`docs/impl/atlas.md` §9).

use agl::develop::develop;
use agl::journal::Journal;

#[test]
fn development_from_nothing() {
    let first = develop(3, 6).text();
    // The reset check: a second run from nothing gives the same bytes.
    assert_eq!(first, develop(3, 6).text());
    // What is read back is what was written.
    let j = Journal::parse(&first).unwrap();
    assert_eq!(j.text(), first);
    assert!(first.len() < 64 * 1024, "{} bytes", first.len());

    // Equal model counts are an observation, not an anchor: equal counts do
    // not prove equal model classes, and this is only one line of evidence.
    let anchored: Vec<_> = j.records.iter().filter(|r| r.anchored).collect();
    assert!(anchored.is_empty());
    let candidate = j
        .records
        .iter()
        .find(|r| r.kind == "species" && r.body.split(" / ").all(|counts| counts == "1,1,1,2,1,2"))
        .expect("the equal-count observation remains in the journal");
    assert!(!candidate.anchored);
    assert!(
        candidate.body.split(" / ").all(|c| c == "1,1,1,2,1,2"),
        "{}",
        candidate.body
    );

    // An edit by hand does not check.
    let edited = first.replacen("1,1,1,2,1,2", "1,1,1,2,1,3", 1);
    assert!(
        Journal::parse(&edited)
            .unwrap_err()
            .contains("does not check")
    );
}
