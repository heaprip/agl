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

    // One species is anchored: the star, by its counts on n = 1..6; its
    // models factor into primes as in §8.
    let anchored: Vec<_> = j.records.iter().filter(|r| r.anchored).collect();
    assert_eq!(anchored.len(), 1);
    assert_eq!(anchored[0].kind, "species");
    assert!(
        anchored[0].body.split(" / ").all(|c| c == "1,1,1,2,1,2"),
        "{}",
        anchored[0].body
    );
    let kinds: Vec<&str> = j
        .records
        .iter()
        .filter(|r| r.kind == "factors")
        .map(|r| r.body.as_str())
        .collect();
    assert_eq!(kinds.iter().filter(|b| **b == "prime").count(), 5);
    assert_eq!(kinds.iter().filter(|b| b.starts_with("1 way")).count(), 2);

    // An edit by hand does not check.
    let edited = first.replacen("1,1,1,2,1,2", "1,1,1,2,1,3", 1);
    assert!(
        Journal::parse(&edited)
            .unwrap_err()
            .contains("does not check")
    );
}
