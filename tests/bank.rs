//! First stage of the clean world (H72, `docs/impl/clean.md`, sections 6 and
//! 6b): the kernel rejects anything ready-made, and the bank of every
//! relation on three elements yields its properties without naming them.
//! The names of the properties live only here, as the reference.

use agl::bank::{Bank, Ext, Kinds, Shape, relations};
use agl::lint::Level;

fn world() -> agl::model::Program {
    agl::parse_file(std::path::Path::new("cases/clean/all3.agl")).unwrap()
}

fn banks(prog: &agl::model::Program, prune: bool) -> Vec<Bank> {
    let (rels, domain, why) = relations(prog);
    assert!(why.is_none());
    assert_eq!(domain.len(), 3);
    rels.into_iter()
        .map(|(r, e)| Bank::grow(r, e, prune))
        .collect()
}

#[test]
fn clean_world_rejects_the_ready_made() {
    let prog = agl::parse_file(std::path::Path::new("cases/clean/ready_made.agl")).unwrap();
    let ready: Vec<usize> = agl::lint::lint(&prog)
        .into_iter()
        .filter(|d| d.code == "ready-made")
        .inspect(|d| assert_eq!(d.level, Level::Error))
        .map(|d| d.line)
        .collect();
    // Every line marked `# ready` in the file, and nothing else.
    let src = std::fs::read_to_string("cases/clean/ready_made.agl").unwrap();
    let marked: Vec<usize> =
        agl::parse::read_expanded(std::path::Path::new("cases/clean/ready_made.agl"))
            .unwrap()
            .lines()
            .enumerate()
            .filter(|(_, l)| l.contains("# ready"))
            .map(|(i, _)| i + 1)
            .collect();
    assert!(src.contains("world clean"));
    assert_eq!(ready, marked);
    assert_eq!(ready.len(), 13);
}

#[test]
fn old_cases_have_nothing_ready_made() {
    for entry in std::fs::read_dir("cases").unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|e| e == "agl") {
            let prog = agl::parse_file(&path).unwrap();
            assert!(prog.clean.is_none());
            assert!(
                agl::lint::lint(&prog)
                    .iter()
                    .all(|d| d.code != "ready-made")
            );
        }
    }
}

fn conv() -> Shape {
    Shape::glue(&Shape::rel(), &Shape::id(), 1, (1, 0))
}

fn comp() -> Shape {
    Shape::glue(&Shape::rel(), &Shape::rel(), 3, (0, 3))
}

fn meet_conv() -> Shape {
    Shape::glue(&Shape::rel(), &Shape::rel(), 6, (0, 1))
}

fn meet_id() -> Shape {
    Shape::glue(&Shape::rel(), &Shape::id(), 5, (0, 0))
}

/// Properties by definition, on pairs of the extent.
fn by_definition(r: &Ext) -> [bool; 5] {
    let n = r.n();
    let all = |f: &dyn Fn(usize, usize) -> bool| (0..n).all(|i| (0..n).all(|j| f(i, j)));
    let refl = (0..n).all(|i| r.get(i, i));
    let irrefl = (0..n).all(|i| !r.get(i, i));
    let sym = all(&|i, j| !r.get(i, j) || r.get(j, i));
    let antisym = all(&|i, j| i == j || !(r.get(i, j) && r.get(j, i)));
    let trans = all(&|i, j| !r.get(i, j) || (0..n).all(|k| !r.get(j, k) || r.get(i, k)));
    [refl, sym, trans, antisym, irrefl]
}

/// The same properties read off the bank: classes ordered by extent. A
/// shape may be missing when only representatives grow, but its class is
/// reached (observational equivalence).
fn by_bank(b: &Bank) -> [bool; 5] {
    let class = |s: &Shape| {
        let e = s.eval(b.ext(0));
        (0..b.classes.len())
            .find(|&c| *b.ext(c) == e)
            .unwrap_or_else(|| panic!("{}: class of {s} not reached", b.rel))
    };
    let le = |s: &Shape, t: &Shape| b.ext(class(s)).subset(b.ext(class(t)));
    let (r, id) = (Shape::rel(), Shape::id());
    [
        le(&id, &r),
        le(&conv(), &r),
        le(&comp(), &r),
        le(&meet_conv(), &id),
        b.ext(class(&meet_id())).count() == 0,
    ]
}

#[test]
fn properties_follow_from_the_bank() {
    let prog = world();
    let banks = banks(&prog, true);
    assert_eq!(banks.len(), 512);
    for b in &banks {
        assert_eq!(by_bank(b), by_definition(b.ext(0)), "{}", b.rel);
    }
}

#[test]
fn pruning_keeps_classes_and_saves_gluings() {
    let prog = world();
    let (pruned, full) = (banks(&prog, true), banks(&prog, false));
    let (mut a, mut b) = (0, 0);
    for (p, f) in pruned.iter().zip(&full) {
        assert_eq!(p.signature(), f.signature(), "{}", p.rel);
        a += p.glued;
        b += f.glued;
    }
    println!("gluings: {a} pruned, {b} without");
    assert!(a < b);
}

#[test]
fn banks_do_not_depend_on_fact_order() {
    let prog = world();
    let base: Vec<String> = banks(&prog, true).iter().map(Bank::signature).collect();
    for seed in 1..=5 {
        let shuffled = agl::sim::permute(&prog, seed);
        let got: Vec<String> = banks(&shuffled, true).iter().map(Bank::signature).collect();
        assert_eq!(got, base, "seed {seed}");
    }
}

#[test]
fn the_bank_names_no_property() {
    let src = include_str!("../src/bank.rs").to_lowercase();
    for word in [
        "reflex",
        "symmetr",
        "transitiv",
        "antisym",
        "poset",
        "partial order",
    ] {
        assert!(!src.contains(word), "{word}");
    }
}

/// Textbook kinds on three elements: their extents, the minimal definition
/// the world gives each, and whether it gets a name.
#[test]
fn textbook_kinds_against_the_world() {
    let prog = world();
    let banks = banks(&prog, true);
    let kinds = Kinds::build(&banks);
    let props: Vec<[bool; 5]> = banks.iter().map(|b| by_definition(b.ext(0))).collect();
    let pick = |f: &dyn Fn(&[bool; 5]) -> bool| -> Vec<usize> {
        (0..props.len()).filter(|&i| f(&props[i])).collect()
    };
    let textbook = [
        ("equivalence", pick(&|p| p[0] && p[1] && p[2]), 5),
        ("partial order", pick(&|p| p[0] && p[3] && p[2]), 19),
        ("preorder", pick(&|p| p[0] && p[2]), 29),
        ("strict order", pick(&|p| p[4] && p[2]), 19),
    ];
    for (name, objs, size) in textbook {
        assert_eq!(objs.len(), size, "{name}");
        let k = kinds.kind_of(&objs);
        let exact = k.extent.iter().collect::<Vec<_>>() == objs;
        println!(
            "{name}: closed {exact}, L = {}, named {}, content {}",
            k.generators.len(),
            k.named,
            k.content.len()
        );
        assert!(exact, "{name} is a concept of the world");
    }
}

/// Post-hoc look at the measure of a name (H72, section 8): where the
/// textbook kinds stand among all concepts by what the definition entails.
#[test]
#[ignore = "diagnostic print; run with --ignored --nocapture"]
fn rank_kinds_by_entailment() {
    let prog = world();
    let banks = banks(&prog, true);
    let kinds = Kinds::build(&banks);
    let props: Vec<[bool; 5]> = banks.iter().map(|b| by_definition(b.ext(0))).collect();
    let set = |f: &dyn Fn(&[bool; 5]) -> bool| -> Vec<usize> {
        (0..props.len()).filter(|&i| f(&props[i])).collect()
    };
    let textbook = [
        ("equivalence", set(&|p| p[0] && p[1] && p[2])),
        ("partial order", set(&|p| p[0] && p[3] && p[2])),
        ("preorder", set(&|p| p[0] && p[2])),
        ("strict order", set(&|p| p[4] && p[2])),
    ];
    let tag = |k: &agl::bank::Kind| {
        let e: Vec<usize> = k.extent.iter().collect();
        textbook
            .iter()
            .find(|(_, s)| *s == e)
            .map_or("", |(n, _)| n)
    };
    type Measure = fn(&agl::bank::Kind) -> isize;
    let measures: [(&str, Measure); 2] = [
        ("content − L", |k| {
            k.content.len() as isize - k.generators.len() as isize
        }),
        ("k·(content − L)", |k| {
            k.extent.count() as isize * (k.content.len() as isize - k.generators.len() as isize)
        }),
    ];
    for (name, m) in measures {
        let mut order: Vec<&agl::bank::Kind> = kinds
            .concepts
            .iter()
            .filter(|k| !k.generators.is_empty())
            .collect();
        order.sort_by_key(|k| std::cmp::Reverse(m(k)));
        println!("by {name}:");
        for (i, k) in order.iter().enumerate() {
            let t = tag(k);
            if i < 12 || !t.is_empty() {
                println!(
                    "  #{} {} k = {}, L = {}, content {} {t}",
                    i + 1,
                    m(k),
                    k.extent.count(),
                    k.generators.len(),
                    k.content.len()
                );
            }
        }
    }
}
