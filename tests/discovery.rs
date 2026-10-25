//! The Bombelli step (H53): what the kernel must hold whatever the search.

use agl::eval::evaluate;
use agl::model::Verdict;
use agl::sim::permute;

fn with_all_pairs() -> agl::model::Program {
    let mut src = std::fs::read_to_string("cases/discovery/bombelli.agl").unwrap();
    for a in -10..=10 {
        for b in -10..=10 {
            src.push_str(&format!(
                "fact p{}_{}: pair(re: {a}, im: {b}) @ pairs\n",
                a + 10,
                b + 10
            ));
        }
    }
    agl::parse(&src).unwrap()
}

fn verdicts(prog: &agl::model::Program) -> Vec<(String, Verdict)> {
    agl::run(prog)
        .queries
        .iter()
        .map(|q| (q.query.atom.to_string(), q.verdict))
        .collect()
}

/// Declared before the run: the formula fails without pairs, 4 is a root,
/// the only integer cube roots are 2 ± i, and their sum brings back 4.
#[test]
fn bombelli_finds_two_plus_i_and_returns_to_four() {
    let prog = with_all_pairs();
    assert_eq!(
        verdicts(&prog),
        [
            ("satisfies(eq: bombelli, x: 4)".to_string(), Verdict::Yes),
            (
                "formula_applies(eq: bombelli)".to_string(),
                Verdict::Unknown
            ),
            (
                "cardano_correct(eq: bombelli, x: 4)".to_string(),
                Verdict::Yes
            ),
        ]
    );
    let out = evaluate(&prog, &prog.planes["pairs"]);
    assert!(!out.truncated, "closure truncated: raise the batch split");
    let roots: Vec<String> = out
        .db
        .values()
        .filter(|(a, _)| a.rel == "cube_root")
        .map(|(a, _)| a.to_string())
        .collect();
    assert_eq!(
        roots,
        [
            "cube_root(eq: bombelli, im: -1, re: 2, sign: minus)",
            "cube_root(eq: bombelli, im: 1, re: 2, sign: plus)"
        ]
    );
}

#[test]
fn bombelli_does_not_depend_on_statement_order() {
    let prog = with_all_pairs();
    let sorted = |p: &agl::model::Program| {
        let mut v = verdicts(p);
        v.sort_by(|x, y| x.0.cmp(&y.0));
        v
    };
    let base = sorted(&prog);
    for seed in 0..3 {
        assert_eq!(base, sorted(&permute(&prog, seed)), "permutation {seed}");
    }
}

/// Step 2 of H57 (Cauchy): the case knows polynomials, the distributive law
/// and reduction modulo X² − s; the planes are the generator's candidates.
fn cauchy() -> agl::model::Program {
    let mut src = std::fs::read_to_string("cases/discovery/cauchy.agl").unwrap();
    let n = |x: i64| {
        if x < 0 {
            format!("m{}", -x)
        } else {
            x.to_string()
        }
    };
    for (p, s) in [
        ("adj_m121", -121),
        ("adj_m1", -1),
        ("adj_0", 0),
        ("adj_1", 1),
    ] {
        let back = if s == -1 { "yes" } else { "unknown" };
        src.push_str(&format!(
            "value repr {p}\nplane {p} = repr:{p}\nfact {p}: adjoined(s: {s}) @ {p}\n\
             query cardano_correct(eq: bombelli, x: 4) @ {p} expect {back}\n"
        ));
    }
    for a in -11..=11 {
        for b in -11..=11 {
            let p = format!("e_{}_{}", n(a), n(b));
            src.push_str(&format!(
                "fact {p}_0: coef(p: {p}, deg: 0, c: {a}) @\nfact {p}_1: coef(p: {p}, deg: 1, c: {b}) @\n"
            ));
        }
    }
    for a in -2..=2 {
        for b in -2..=2 {
            for c in -2..=2 {
                for d in -2..=2 {
                    let (l, r) = (
                        format!("e_{}_{}", n(a), n(b)),
                        format!("e_{}_{}", n(c), n(d)),
                    );
                    src.push_str(&format!("fact pr_{l}_{r}: probe(l: {l}, r: {r}) @\n"));
                }
            }
        }
    }
    agl::parse(&src).unwrap()
}

fn atoms(out: &agl::eval::Outcome, rel: &str) -> Vec<agl::model::Atom> {
    out.db
        .values()
        .map(|(a, _)| a.clone())
        .filter(|a| a.rel == rel && !a.neg)
        .collect()
}

fn num(a: &agl::model::Atom, role: &str) -> i64 {
    match a.args.iter().find(|(r, _)| r == role) {
        Some((_, agl::model::Term::Num(x, _))) => *x as i64,
        _ => panic!("{a}: no number `{role}`"),
    }
}

/// Declared before the run (H57, step 2): only X² = −1 returns to 4; the
/// products it derives are Hamilton's, which the case does not contain;
/// the roots are 2 ± X; no law is broken under any candidate.
#[test]
fn cauchy_adjoins_minus_one_and_derives_hamilton() {
    let prog = cauchy();
    let report = agl::run(&prog);
    assert_eq!(report.failed_queries().count(), 1, "only the anomaly fails");
    let coef = |p: &str, deg: i64| {
        let (a, b) = p.trim_start_matches("e_").split_once('_').unwrap();
        let v = |s: &str| {
            s.strip_prefix('m')
                .map_or_else(|| s.parse::<i64>().unwrap(), |x| -x.parse::<i64>().unwrap())
        };
        if deg == 0 { v(a) } else { v(b) }
    };
    for (p, s) in [
        ("adj_m121", -121),
        ("adj_m1", -1),
        ("adj_0", 0),
        ("adj_1", 1),
    ] {
        let out = evaluate(&prog, &prog.planes[p]);
        assert!(!out.truncated, "closure truncated: raise the batch split");
        assert_eq!(atoms(&out, "law_broken"), [], "{p}");
        let sqrt = !atoms(&out, "sqrt_of").is_empty();
        assert_eq!(sqrt, s < 0, "{p}: square root of -121");
        let roots: Vec<String> = atoms(&out, "cube_root")
            .iter()
            .map(|a| a.to_string())
            .collect();
        if s == -1 {
            assert_eq!(
                roots,
                [
                    "cube_root(eq: bombelli, p: e_2_1, sign: plus)",
                    "cube_root(eq: bombelli, p: e_2_m1, sign: minus)"
                ]
            );
        } else {
            assert_eq!(roots, Vec::<String>::new(), "{p}");
        }
        let products: Vec<_> = atoms(&out, "reduced")
            .into_iter()
            .filter(|a| a.to_string().contains("kind: product"))
            .collect();
        assert_eq!(products.len(), 2 * 625);
        for a in products {
            let name = |role: &str| match a.args.iter().find(|(r, _)| r == role) {
                Some((_, agl::model::Term::Sym(x))) => x.clone(),
                _ => panic!(),
            };
            let (l, r) = (name("l"), name("r"));
            let (x0, x1, y0, y1) = (coef(&l, 0), coef(&l, 1), coef(&r, 0), coef(&r, 1));
            let want = if num(&a, "deg") == 0 {
                x0 * y0 + s * x1 * y1
            } else {
                x0 * y1 + x1 * y0
            };
            assert_eq!(num(&a, "c"), want, "{p}: {a}");
        }
    }
}

#[test]
fn cauchy_does_not_depend_on_statement_order() {
    let prog = cauchy();
    let sorted = |p: &agl::model::Program| {
        let mut v: Vec<(String, Verdict)> = agl::run(p)
            .queries
            .iter()
            .map(|q| (format!("{} @ {:?}", q.query.atom, q.plane), q.verdict))
            .collect();
        v.sort_by(|x, y| x.0.cmp(&y.0));
        v
    };
    let base = sorted(&prog);
    for seed in 0..2 {
        assert_eq!(base, sorted(&permute(&prog, seed)), "permutation {seed}");
    }
}

/// Step 3 of H57: the adjoining library, one problem at a time. Elements
/// a + bX over the domain, multipliers |k| <= 5, probes among |a|, |b| <= 2
/// (or 0..4 for the naturals); `adjoin` adds the plane where the equation is
/// adjoined, whether or not it failed.
fn adjoined(problem: &str) -> agl::model::Program {
    let path = format!("cases/discovery/adjoin/{problem}.agl");
    let mut src = agl::read_expanded(std::path::Path::new(&path)).unwrap();
    let n = |x: i64| {
        if x < 0 {
            format!("m{}", -x)
        } else {
            x.to_string()
        }
    };
    let (lo, hi, plo, phi) = if problem == "negatives" {
        (0, 8, 0, 4)
    } else {
        (-4, 4, -2, 2)
    };
    let eq = agl::parse(&src)
        .unwrap()
        .facts
        .iter()
        .find(|f| f.atom.rel == "equation")
        .unwrap()
        .atom
        .args[0]
        .1
        .to_string();
    src.push_str(&format!(
        "axis repr\nvalue repr adj\nplane adj = repr:adj\nfact adj: adjoined(eq: {eq}) @ adj\n"
    ));
    for a in lo..=hi {
        for b in lo..=hi {
            let p = format!("e_{}_{}", n(a), n(b));
            src.push_str(&format!(
                "fact {p}_0: coef(p: {p}, deg: 0, c: {a}) @\nfact {p}_1: coef(p: {p}, deg: 1, c: {b}) @\n"
            ));
        }
    }
    for a in -5..=5 {
        for b in -5..=5 {
            let u = format!("u_{}_{}", n(a), n(b));
            src.push_str(&format!(
                "fact {u}_0: mult(u: {u}, deg: 0, c: {a}) @\nfact {u}_1: mult(u: {u}, deg: 1, c: {b}) @\n"
            ));
        }
    }
    let small: Vec<String> = (plo..=phi)
        .flat_map(|a| (plo..=phi).map(move |b| (a, b)))
        .map(|(a, b)| format!("e_{}_{}", n(a), n(b)))
        .collect();
    for l in &small {
        for r in &small {
            src.push_str(&format!("fact pr_{l}_{r}: probe(l: {l}, r: {r}) @\n"));
        }
    }
    agl::parse(&src).unwrap()
}

/// What the sieve sees in the adjoined plane: solutions, and the laws
/// broken with how often.
fn sieve(prog: &agl::model::Program) -> (Vec<String>, Vec<(String, usize)>) {
    let out = evaluate(prog, &prog.planes["adj"]);
    assert!(!out.truncated, "closure truncated: raise the batch split");
    let sym = |a: &agl::model::Atom, role: &str| {
        a.args
            .iter()
            .find(|(r, _)| r == role)
            .unwrap()
            .1
            .to_string()
    };
    let sols = atoms(&out, "solution")
        .iter()
        .map(|a| sym(a, "p"))
        .collect();
    let mut laws = std::collections::BTreeMap::new();
    for a in atoms(&out, "law_broken") {
        *laws.entry(sym(&a, "law")).or_insert(0) += 1;
    }
    (sols, laws.into_iter().collect())
}

/// Declared before the run (H57, step 3): negatives and fractions pass the
/// sieve; 1 : 0 breaks conservativity; a superfluous x² = 4 gives zero
/// divisors; blind, on the frozen library, √2 and i pass with roots ±X.
#[test]
fn one_adjoining_mechanism_for_four_extensions() {
    let s = |v: &[&str]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>();
    let none: Vec<(String, usize)> = vec![];
    let cases = [
        (
            "negatives",
            s(&["e_0_1", "e_2_2", "e_4_3", "e_6_4", "e_8_5"]),
            none.clone(),
        ),
        ("fractions", s(&["e_0_1", "e_1_m2", "e_m1_4"]), none.clone()),
        ("sqrt_two", s(&["e_0_1", "e_0_m1"]), none.clone()),
        ("imaginary", s(&["e_0_1", "e_0_m1"]), none.clone()),
    ];
    for (p, sols, laws) in cases {
        let prog = adjoined(p);
        let failed: Vec<_> = agl::run(&prog)
            .failed_queries()
            .map(|q| q.plane.is_empty())
            .collect();
        assert_eq!(failed, [true], "{p}: the anomaly at the root");
        assert_eq!(sieve(&prog), (sols, laws), "{p}");
    }
    let (_, laws) = sieve(&adjoined("divide_by_zero"));
    assert_eq!(laws, [("conservative".to_string(), 60)]);
    let prog = adjoined("square_four");
    assert_eq!(
        agl::run(&prog).failed_queries().count(),
        0,
        "x² = 4 solves already"
    );
    let (_, laws) = sieve(&prog);
    assert_eq!(
        laws.iter().map(|l| l.0.as_str()).collect::<Vec<_>>(),
        ["cancellation"]
    );
}

#[test]
fn adjoining_does_not_depend_on_statement_order() {
    for p in ["fractions", "square_four"] {
        let prog = adjoined(p);
        let base = sieve(&prog);
        for seed in 0..2 {
            assert_eq!(
                base,
                sieve(&permute(&prog, seed)),
                "{p}, permutation {seed}"
            );
        }
    }
}

/// Legacy H57 star, not a soup-derived discovery: this helper explicitly
/// enumerates the three signed cyclic products, expands them to complete
/// tables, and supplies every probe. The active laws only sieve those tables.
///
/// The next functional seam must replace this generator with generic table
/// candidates whose primary constraints are represented as entities and
/// evidence in the metacore. `atlas::Law` currently has no named constants or
/// coefficient-valued products, while `bank` and `layer` generate binary
/// query extents rather than finite operation tables. Until those generic
/// interfaces meet, this test is a regression check for the old sieve only;
/// it does not establish that quaternions are inferred from the soup.
fn hamilton(active: &[&str]) -> (agl::model::Program, Vec<String>) {
    let mut src = std::fs::read_to_string("cases/discovery/hamilton.agl").unwrap();
    for u in 0..4 {
        src.push_str(&format!("fact unit_{u}: unit(u: u{u}) @\n"));
        if u > 0 {
            src.push_str(&format!("fact sq_{u}: fixed_square(u: u{u}) @\n"));
        }
    }
    for l in active {
        src.push_str(&format!("fact active_{l}: active(law: {l}) @\n"));
    }
    for i in 0..8 {
        let s = |k: usize| if i >> k & 1 == 0 { 1 } else { -1 };
        let t = format!("f{i}");
        src.push_str(&format!("fact {t}: table(t: {t}, scope: all) @\n"));
        for (k, (a, b, c)) in [(1, 2, 3), (2, 3, 1), (3, 1, 2)].into_iter().enumerate() {
            src.push_str(&format!(
                "fact {t}_{a}{b}: entry(t: {t}, a: u{a}, b: u{b}, s: {}, c: u{c}) @\n\
                 fact {t}_{b}{a}: entry(t: {t}, a: u{b}, b: u{a}, s: {}, c: u{c}) @\n",
                s(k),
                -s(k)
            ));
        }
    }
    let mut elems = Vec::new();
    for a in 0..4 {
        for b in a + 1..4 {
            for (ca, cb) in [(1, 1), (1, -1)] {
                let p = format!("x_{a}{b}_{}", if cb > 0 { "p" } else { "m" });
                src.push_str(&format!(
                    "fact {p}_a: coef(p: {p}, u: u{a}, c: {ca}) @\nfact {p}_b: coef(p: {p}, u: u{b}, c: {cb}) @\n"
                ));
                elems.push(p);
            }
        }
    }
    for x in &elems {
        for y in &elems {
            src.push_str(&format!(
                "fact pr_{x}_{y}: probe(scope: all, x: {x}, y: {y}) @\n"
            ));
        }
    }
    let prog = agl::parse(&src).unwrap();
    let out = evaluate(&prog, &agl::model::Plane::new());
    assert!(!out.truncated, "closure truncated: raise the batch split");
    let alive = atoms(&out, "survives")
        .iter()
        .map(|a| a.args[0].1.to_string())
        .collect();
    (prog, alive)
}

/// Declared before the run (H57, step 4): with commutativity dropped, of the
/// eight tables exactly two survive — ij = k, jk = i, ki = j (f0) and its
/// mirror with every sign flipped (f7); with every law kept, none.
#[test]
fn hamilton_drops_commutativity_and_finds_quaternions() {
    assert_eq!(hamilton(&["associative", "norm"]).1, ["f0", "f7"]);
    assert_eq!(
        hamilton(&["commutative", "associative", "norm"]).1,
        Vec::<String>::new()
    );
    assert_eq!(
        hamilton(&["commutative", "associative"]).1,
        Vec::<String>::new()
    );
}

#[test]
fn hamilton_does_not_depend_on_statement_order() {
    let (prog, alive) = hamilton(&["associative", "norm"]);
    for seed in 0..2 {
        let p = permute(&prog, seed);
        let out = evaluate(&p, &agl::model::Plane::new());
        assert!(!out.truncated, "closure truncated: raise the batch split");
        let got: Vec<String> = atoms(&out, "survives")
            .iter()
            .map(|a| a.args[0].1.to_string())
            .collect();
        assert_eq!(alive, got, "permutation {seed}");
    }
}
