//! Deterministic simulation support, in the spirit of FoundationDB's
//! simulation testing: every source of variation comes from one explicit seed,
//! so any failing run is replayed exactly by its seed.

use crate::model::*;

/// SplitMix64: small, fast, and identical on every platform.
#[derive(Clone, Debug)]
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform in `0..n`; `n` must be positive.
    pub fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }

    pub fn chance(&mut self, num: u64, den: u64) -> bool {
        self.next_u64() % den < num
    }

    pub fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }

    pub fn shuffle<T>(&mut self, xs: &mut [T]) {
        for i in (1..xs.len()).rev() {
            xs.swap(i, self.below(i + 1));
        }
    }
}

const RELS: [&str; 4] = ["p", "q", "r", "s"];
const ROLES: [&str; 2] = ["a", "b"];
const CONSTS: [&str; 3] = ["c0", "c1", "c2"];

/// The value tree used by generated programs: one axis `w` with
/// `root ⊃ {x ⊃ {x1, x2}, y}` and an overlap between `x2` and `y`.
const VALUES: [&str; 5] = ["root", "x", "x1", "x2", "y"];

fn gen_plane(rng: &mut Rng) -> Plane {
    if rng.chance(1, 5) {
        return Plane::new();
    }
    Plane::from([("w".to_string(), rng.pick(&VALUES).to_string())])
}

fn gen_atom(rng: &mut Rng, vars: &[&str]) -> Atom {
    let rel = rng.pick(&RELS).to_string();
    let args = ROLES
        .iter()
        .map(|role| {
            let term = if !vars.is_empty() && rng.chance(1, 2) {
                Term::Var(rng.pick(vars).to_string())
            } else {
                Term::Sym(rng.pick(&CONSTS).to_string())
            };
            (role.to_string(), term)
        })
        .collect();
    Atom::new(rel, args, rng.chance(1, 3))
}

/// A random, lint-clean program: small vocabulary, so derivations and
/// conflicts actually meet.
pub fn gen_program(seed: u64) -> Program {
    let mut rng = Rng::new(seed);
    let mut prog = Program::default();
    prog.axes.declare_axis("w");
    prog.axes.declare_value("w", "root", None).unwrap();
    prog.axes.declare_value("w", "x", Some("root")).unwrap();
    prog.axes.declare_value("w", "x1", Some("x")).unwrap();
    prog.axes.declare_value("w", "x2", Some("x")).unwrap();
    prog.axes.declare_value("w", "y", Some("root")).unwrap();
    prog.axes.declare_overlap("w", "x2", "y").unwrap();

    let statuses = ["hi", "mid", "lo", "given"];
    if rng.chance(1, 2) {
        prog.status_rank = [("hi", 3), ("mid", 2), ("lo", 1)]
            .into_iter()
            .map(|(s, r)| (s.to_string(), r))
            .collect();
    }
    for i in 0..(3 + rng.below(8)) {
        let atom = gen_atom(&mut rng, &[]);
        let status = rng.pick(&statuses).to_string();
        prog.facts.push(Fact {
            id: format!("f{i}"),
            atom,
            plane: gen_plane(&mut rng),
            status,
            line: 0,
        });
    }
    for i in 0..(2 + rng.below(6)) {
        let n_body = 1 + rng.below(2);
        let body: Vec<Atom> = (0..n_body)
            .map(|_| gen_atom(&mut rng, &["X", "Y"]))
            .collect();
        let bound: Vec<&str> = body.iter().flat_map(|a| a.vars()).collect();
        let mut head = gen_atom(&mut rng, &bound);
        if bound.is_empty() {
            head.args.iter_mut().for_each(|(_, t)| {
                if matches!(t, Term::Var(_)) {
                    *t = Term::Sym("c0".into());
                }
            });
        }
        let strength = if rng.chance(1, 3) {
            Strength::Strict
        } else {
            Strength::Defeasible
        };
        prog.rules.push(Rule {
            id: format!("r{i}"),
            head,
            body: body.into_iter().map(Lit::Atom).collect(),
            strength,
            plane: gen_plane(&mut rng),
            line: 0,
        });
    }
    let n_rules = prog.rules.len();
    for _ in 0..rng.below(3) {
        let (w, l) = (rng.below(n_rules), rng.below(n_rules));
        if w != l {
            prog.defeats.insert((format!("r{w}"), format!("r{l}")));
        }
    }
    if rng.chance(1, 3) {
        let atom = gen_atom(&mut rng, &["X", "Y"]);
        let plane = gen_plane(&mut rng);
        prog.forbids.push(Forbid {
            atom,
            plane,
            line: 0,
        });
    }
    // Contexts situated by facts or by rules, sometimes into disjoint values.
    let contexts = ["k0", "k1"];
    for i in 0..rng.below(3) {
        let ctx = rng.pick(&contexts).to_string();
        let value = rng.pick(&VALUES).to_string();
        let atom = Atom::new(
            "situated".into(),
            vec![
                ("context".into(), Term::Sym(ctx)),
                ("axis".into(), Term::Sym("w".into())),
                ("value".into(), Term::Sym(value)),
            ],
            false,
        );
        prog.facts.push(Fact {
            id: format!("sit{i}"),
            atom,
            plane: gen_plane(&mut rng),
            status: "given".into(),
            line: 0,
        });
    }
    for _ in 0..(3 + rng.below(6)) {
        let situate = rng.chance(1, 3).then(|| rng.pick(&contexts).to_string());
        prog.queries.push(Query {
            atom: gen_atom(&mut rng, &[]),
            plane: gen_plane(&mut rng),
            situate,
            expect: None,
            heldout: false,
            line: 0,
        });
    }
    prog
}

/// Reorders every statement list of the program with the given seed.
pub fn permute(prog: &Program, seed: u64) -> Program {
    let mut rng = Rng::new(seed);
    let mut facts = prog.facts.clone();
    let mut rules = prog.rules.clone();
    let mut queries = prog.queries.clone();
    rng.shuffle(&mut facts);
    rng.shuffle(&mut rules);
    rng.shuffle(&mut queries);
    for r in &mut rules {
        rng.shuffle(&mut r.body);
        for lit in &mut r.body {
            if let Lit::Agg { over, .. } = lit {
                rng.shuffle(over);
            }
        }
    }
    let mut p = prog.clone();
    p.facts = facts;
    p.rules = rules;
    p.queries = queries;
    p
}
