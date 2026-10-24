//! Reflection R2: proposals of structural changes.

use agl::propose::{Op, apply, propose};

fn load(path: &str) -> agl::model::Program {
    agl::parse::parse_file(std::path::Path::new(path)).unwrap()
}

#[test]
fn two_exceptions_get_an_intermediate_plane() {
    let prog = load("cases/reflection/two-exceptions.agl");
    let (ps, _) = propose(&prog);
    let top = ps.first().expect("a proposal");
    match &top.op {
        Op::Intermediate {
            axis,
            parent,
            children,
            rule,
            ..
        } => {
            assert_eq!(axis, "taxon");
            assert_eq!(parent, "Insecta");
            assert_eq!(
                children,
                &vec!["Chironomidae_larvae".to_string(), "Plecoptera".to_string()]
            );
            assert_eq!(rule, "ex1");
        }
        other => panic!("expected an intermediate plane, got {other:?}"),
    }
    assert_eq!((top.before, top.after), (0, 4));
    assert!(top.remaining.is_empty());

    // The change itself meets every expectation and adds no conflict.
    let changed = apply(&prog, &top.op).unwrap();
    let report = agl::run(&changed);
    assert!(!report.has_errors());
    assert!(report.failed_queries().next().is_none());
    assert!(report.conflicts.is_empty());
}

#[test]
fn patched_rules_parse_back() {
    let prog = load("cases/reflection/two-exceptions.agl");
    let (ps, _) = propose(&prog);
    let added: Vec<&str> = ps[0]
        .patch
        .lines()
        .filter_map(|l| l.strip_prefix("+ "))
        .collect();
    let src = format!(
        "axis taxon\nvalue taxon Insecta\n{}\n",
        added.join(
            "
"
        )
    );
    // Values must be declared parent-first: the new value precedes its children.
    let prog2 = agl::parse(&src).unwrap_or_else(|e| panic!("{e}\n{src}"));
    assert_eq!(prog2.rules.len(), 1);
    assert_eq!(
        prog2.rules[0].to_source(),
        added.last().unwrap().to_string()
    );
}

#[test]
fn an_exception_with_more_conditions_gets_a_defeat() {
    let src = "
axis taxon
value taxon Insecta
plane insects = taxon:Insecta
fact i1: insect(organism: locust) @ insects
fact i2: insect(organism: midge_larva) @ insects
fact i3: has_hemoglobin(organism: midge_larva) @ insects
rule r_ins defeasible @ insects: ¬transports_o2(organism: ?x) <- insect(organism: ?x)
rule ex1 defeasible @ insects: transports_o2(organism: ?x) <- insect(organism: ?x), has_hemoglobin(organism: ?x)
query transports_o2(organism: locust) @ insects expect no
query transports_o2(organism: midge_larva) @ insects expect yes
";
    let (ps, _) = propose(&agl::parse(src).unwrap());
    let top = ps.first().expect("a proposal");
    assert_eq!(
        top.op,
        Op::Defeats {
            winner: "ex1".into(),
            loser: "r_ins".into(),
            by_body: true
        }
    );
    assert_eq!((top.before, top.after), (1, 2));
}

#[test]
fn current_cases_need_no_proposals() {
    let mut paths: Vec<_> = std::fs::read_dir("cases")
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    paths.sort();
    for path in paths
        .iter()
        .filter(|p| p.extension().is_some_and(|e| e == "agl"))
    {
        let (ps, notes) = propose(&load(path.to_str().unwrap()));
        assert!(
            ps.is_empty() && notes.is_empty(),
            "{}: {ps:?} {notes:?}",
            path.display()
        );
    }
}
