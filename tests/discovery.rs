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
