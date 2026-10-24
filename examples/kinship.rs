//! Kinship terms decomposed over grouped axes: a prototype outside the kernel
//! (docs/cases/kinship.md, H42, H44).
//!
//! Level 0 is the exact path from ego to the relative over three primitive
//! steps: parent `P`, child `C` and spouse `S`, each with the sex of the person
//! it reaches. `P` directly followed by `C` is a sibling: the parent's other
//! child. Level 1 groups the axes into a shape: generation, degree, affinity,
//! lineality, line and sex. Level 2 is a class over the shape: blood relative,
//! in-law, ancestor. A term is a union of paths.
//!
//! Sex is finite, so every pattern expands into specific paths, and
//! subsumption at every level is inclusion of the expanded sets. The run checks
//! the laws that tie the levels together and answers questions whose answers
//! are known; any mismatch fails it.

use std::collections::BTreeSet;
use std::process::ExitCode;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Step {
    P,
    C,
    S,
}

/// Sex of a person; `X` is either.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Sex {
    M,
    F,
    X,
}

impl Sex {
    fn parse(s: &str) -> Sex {
        match s {
            "m" => Sex::M,
            "f" => Sex::F,
            "x" | "" => Sex::X,
            _ => panic!("sex {s:?}"),
        }
    }

    fn mark(self) -> &'static str {
        match self {
            Sex::M => "m",
            Sex::F => "f",
            Sex::X => "x",
        }
    }

    fn specific(self) -> Vec<Sex> {
        match self {
            Sex::X => vec![Sex::M, Sex::F],
            s => vec![s],
        }
    }

    fn join(self, other: Sex) -> Sex {
        if self == other { self } else { Sex::X }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Path {
    ego: Sex,
    steps: Vec<(Step, Sex)>,
}

impl Path {
    /// `m| Sf Pm`: an optional ego sex, then steps with the sex they reach.
    fn parse(s: &str) -> Path {
        let (ego, rest) = match s.split_once('|') {
            Some((e, r)) => (Sex::parse(e.trim()), r),
            None => (Sex::X, s),
        };
        let steps = rest
            .split_whitespace()
            .map(|t| {
                let (k, x) = t.split_at(1);
                let k = match k {
                    "P" => Step::P,
                    "C" => Step::C,
                    "S" => Step::S,
                    _ => panic!("step {t:?}"),
                };
                (k, Sex::parse(x))
            })
            .collect();
        Path { ego, steps }
    }

    fn show(&self) -> String {
        let steps: Vec<_> = self
            .steps
            .iter()
            .map(|(k, x)| format!("{k:?}{}", x.mark()))
            .collect();
        match self.ego {
            Sex::X => steps.join(" "),
            e => format!("{}| {}", e.mark(), steps.join(" ")),
        }
    }

    /// Every specific path the pattern stands for.
    fn expand(&self) -> Vec<Path> {
        let mut out: Vec<Path> = self
            .ego
            .specific()
            .into_iter()
            .map(|ego| Path { ego, steps: vec![] })
            .collect();
        for &(k, x) in &self.steps {
            out = out
                .into_iter()
                .flat_map(|p| {
                    x.specific().into_iter().map(move |x| {
                        let mut q = p.clone();
                        q.steps.push((k, x));
                        q
                    })
                })
                .collect();
        }
        out
    }

    fn count(&self, k: Step) -> i32 {
        self.steps.iter().filter(|s| s.0 == k).count() as i32
    }

    /// Level 1: the grouped axes.
    fn shape(&self) -> Shape {
        let (p, c, s) = (
            self.count(Step::P),
            self.count(Step::C),
            self.count(Step::S),
        );
        Shape {
            generation: p - c,
            degree: p + c,
            affinal: s > 0,
            lineal: s == 0 && (p == 0 || c == 0),
            line: match self.steps.first() {
                Some(&(Step::P, x)) => Some(x),
                _ => None,
            },
            sex: self.steps.last().map_or(self.ego, |s| s.1),
        }
    }

    /// `P C P` → `P`: a sibling's parent is one's own parent. A default:
    /// half-siblings and step-parents are the exceptions.
    fn fold_default(&self) -> Path {
        let mut steps = self.steps.clone();
        while let Some(i) = (0..steps.len().saturating_sub(2)).find(|&i| {
            steps[i].0 == Step::P && steps[i + 1].0 == Step::C && steps[i + 2].0 == Step::P
        }) {
            let last = steps[i + 2];
            steps.splice(i..i + 3, [last]);
        }
        Path {
            ego: self.ego,
            steps,
        }
    }

    fn then(&self, next: &Path) -> Path {
        let mut steps = self.steps.clone();
        steps.extend(&next.steps);
        Path {
            ego: self.ego,
            steps,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Shape {
    generation: i32,
    degree: i32,
    affinal: bool,
    lineal: bool,
    /// Sex of the first parent when the path starts upward.
    line: Option<Sex>,
    sex: Sex,
}

/// Level 2 classes, defined on the shape.
#[derive(Clone, Copy, Debug)]
enum Class {
    Blood,
    InLaw,
    Ancestor,
    Descendant,
}

impl Class {
    fn name(self) -> &'static str {
        match self {
            Class::Blood => "кровный родственник",
            Class::InLaw => "свойственник",
            Class::Ancestor => "предок",
            Class::Descendant => "потомок",
        }
    }

    fn of_shape(self, s: &Shape) -> bool {
        match self {
            Class::Blood => !s.affinal,
            Class::InLaw => s.affinal,
            Class::Ancestor => s.lineal && s.generation > 0,
            Class::Descendant => s.lineal && s.generation < 0,
        }
    }

    /// The same class written straight on level 0, independently.
    fn of_path(self, p: &Path) -> bool {
        let all = |k| !p.steps.is_empty() && p.steps.iter().all(|s| s.0 == k);
        match self {
            Class::Blood => p.steps.iter().all(|s| s.0 != Step::S),
            Class::InLaw => p.steps.iter().any(|s| s.0 == Step::S),
            Class::Ancestor => all(Step::P),
            Class::Descendant => all(Step::C),
        }
    }
}

const CLASSES: [Class; 4] = [
    Class::Blood,
    Class::InLaw,
    Class::Ancestor,
    Class::Descendant,
];

struct Term {
    lang: &'static str,
    name: &'static str,
    senses: Vec<Path>,
}

impl Term {
    fn level0(&self) -> BTreeSet<Path> {
        self.senses.iter().flat_map(Path::expand).collect()
    }

    fn level1(&self) -> BTreeSet<Shape> {
        self.level0().iter().map(Path::shape).collect()
    }

    fn show(&self) -> String {
        let s: Vec<_> = self.senses.iter().map(Path::show).collect();
        s.join(" + ")
    }
}

const TERMS: &[(&str, &str, &str)] = &[
    ("ru", "мать", "Pf"),
    ("ru", "отец", "Pm"),
    ("ru", "родитель", "Px"),
    ("ru", "сын", "Cm"),
    ("ru", "дочь", "Cf"),
    ("ru", "ребёнок", "Cx"),
    ("ru", "брат", "Px Cm"),
    ("ru", "сестра", "Px Cf"),
    ("ru", "дед", "Px Pm"),
    ("ru", "бабушка", "Px Pf"),
    ("ru", "прадед", "Px Px Pm"),
    ("ru", "внук", "Cx Cm"),
    ("ru", "дядя", "Px Px Cm + Px Px Cf Sm"),
    ("ru", "тётя", "Px Px Cf + Px Px Cm Sf"),
    ("ru", "двоюродный брат", "Px Px Cx Cm"),
    ("ru", "муж", "Sm"),
    ("ru", "жена", "Sf"),
    ("ru", "тесть", "Sf Pm"),
    ("ru", "тёща", "Sf Pf"),
    ("ru", "свёкор", "Sm Pm"),
    ("ru", "свекровь", "Sm Pf"),
    ("ru", "отчим", "Pf Sm"),
    ("ru", "мачеха", "Pm Sf"),
    ("ru", "деверь", "Sm Px Cm"),
    ("ru", "шурин", "Sf Px Cm"),
    ("ru", "зять", "Cf Sm + Px Cf Sm"),
    ("ru", "брат матери", "Pf Px Cm"),
    ("ru", "мать брата", "Px Cm Pf"),
    ("ru", "дядя (кровный)", "Px Px Cm"),
    ("en", "parent", "Px"),
    ("en", "grandfather", "Px Pm"),
    ("en", "sibling", "Px Cx"),
    ("en", "uncle", "Px Px Cm + Px Px Cf Sm"),
    ("en", "cousin", "Px Px Cx Cx"),
    ("en", "father-in-law", "Sx Pm"),
    ("en", "mother-in-law", "Sx Pf"),
    ("la", "patruus", "Pm Px Cm"),
    ("la", "avunculus", "Pf Px Cm"),
    ("la", "amita", "Pm Px Cf"),
    ("la", "matertera", "Pf Px Cf"),
];

fn terms() -> Vec<Term> {
    TERMS
        .iter()
        .map(|&(lang, name, def)| Term {
            lang,
            name,
            senses: def.split('+').map(Path::parse).collect(),
        })
        .collect()
}

/// The most specific pattern covering both terms: paths with the same steps
/// are joined sex by sex (the "greatest common divisor").
fn common(a: &Term, b: &Term) -> String {
    let mut groups: Vec<Path> = vec![];
    for p in a.level0().iter().chain(b.level0().iter()) {
        let kinds: Vec<_> = p.steps.iter().map(|s| s.0).collect();
        match groups
            .iter_mut()
            .find(|g| g.steps.iter().map(|s| s.0).eq(kinds.iter().copied()))
        {
            Some(g) => {
                g.ego = g.ego.join(p.ego);
                for (gs, ps) in g.steps.iter_mut().zip(&p.steps) {
                    gs.1 = gs.1.join(ps.1);
                }
            }
            None => groups.push(p.clone()),
        }
    }
    groups.sort();
    let s: Vec<_> = groups.iter().map(Path::show).collect();
    s.join(" + ")
}

fn main() -> ExitCode {
    let terms = terms();
    let get = |name: &str| {
        terms
            .iter()
            .find(|t| t.name == name)
            .unwrap_or_else(|| panic!("term {name}"))
    };
    let mut bad = 0;

    println!("# Термины\n");
    for t in &terms {
        println!("{} {:<16} {}", t.lang, t.name, t.show());
    }

    // Law 1: projection keeps subsumption. What projection loses is listed.
    let mut subsumed = 0;
    let mut lost = vec![];
    for a in &terms {
        for b in &terms {
            let (a0, b0, a1, b1) = (a.level0(), b.level0(), a.level1(), b.level1());
            if a0.is_subset(&b0) {
                subsumed += 1;
                if !a1.is_subset(&b1) {
                    bad += 1;
                    println!(
                        "НАРУШЕНО: {} ⊑ {} на уровне 0, но не на уровне 1",
                        a.name, b.name
                    );
                }
            }
            if a.name < b.name && a0 != b0 && a1 == b1 {
                lost.push(format!("{} = {}", a.name, b.name));
            }
        }
    }
    println!("\n# Законы\n");
    println!(
        "1. Проекция сохраняет подчинение: {subsumed} пар ⊑ на уровне 0, все сохранились на уровне 1."
    );
    println!(
        "   Равны на уровне 1, различаются на уровне 0: {}.",
        lost.join("; ")
    );

    // Law 2: a class through the shape equals the same class written on paths.
    let paths: BTreeSet<Path> = terms.iter().flat_map(Term::level0).collect();
    let mut checked = 0;
    for p in &paths {
        for c in CLASSES {
            checked += 1;
            if c.of_shape(&p.shape()) != c.of_path(p) {
                bad += 1;
                println!(
                    "НАРУШЕНО: {} для {}: через уровень 1 и напрямую — по-разному",
                    c.name(),
                    p.show()
                );
            }
        }
    }
    println!(
        "2. Класс через уровень 1 равен классу, записанному прямо на путях: {checked} проверок."
    );

    // Law 3: composing paths adds generation and degree, like multiplying
    // numbers adds exponents. Lineality is not additive.
    let (mut composed, mut not_lineal) = (0, 0);
    for p in &paths {
        for q in &paths {
            let r = p.then(q);
            let (sp, sq, sr) = (p.shape(), q.shape(), r.shape());
            composed += 1;
            if sr.generation != sp.generation + sq.generation
                || sr.degree != sp.degree + sq.degree
                || sr.affinal != (sp.affinal || sq.affinal)
            {
                bad += 1;
                println!("НАРУШЕНО: состав {} · {}", p.show(), q.show());
            }
            if sp.lineal && sq.lineal && !sr.lineal {
                not_lineal += 1;
            }
        }
    }
    println!(
        "3. Состав путей складывает поколение и степень: {composed} пар. Прямая линия не складывается: {not_lineal} пар прямых дают боковой (родитель · ребёнок = брат)."
    );

    let le0 = |a: &str, b: &str| get(a).level0().is_subset(&get(b).level0());
    let eq0 = |a: &str, b: &str| get(a).level0() == get(b).level0();
    let eq1 = |a: &str, b: &str| get(a).level1() == get(b).level1();
    let union0 = |a: &str, b: &str| -> BTreeSet<Path> {
        get(a).level0().union(&get(b).level0()).cloned().collect()
    };
    let union1 = |a: &str, b: &str| -> BTreeSet<Shape> {
        get(a).level1().union(&get(b).level1()).cloned().collect()
    };
    let all = |a: &str, c: Class| get(a).level1().iter().all(|s| c.of_shape(s));
    let some = |a: &str, c: Class| get(a).level1().iter().any(|s| c.of_shape(s));
    let folded =
        |a: &str| -> BTreeSet<Path> { get(a).level0().iter().map(Path::fold_default).collect() };

    let questions: Vec<(&str, bool, bool)> = vec![
        ("мать ⊑ родитель", le0("мать", "родитель"), true),
        ("мать — предок", all("мать", Class::Ancestor), true),
        ("дед — предок", all("дед", Class::Ancestor), true),
        ("отчим — предок", all("отчим", Class::Ancestor), false),
        ("внук — потомок", all("внук", Class::Descendant), true),
        ("тёща — свойственник", all("тёща", Class::InLaw), true),
        (
            "тёща — кровный родственник",
            all("тёща", Class::Blood),
            false,
        ),
        (
            "дядя — кровный родственник",
            all("дядя", Class::Blood),
            false,
        ),
        ("дядя — свойственник", all("дядя", Class::InLaw), false),
        (
            "у дяди есть кровный смысл",
            some("дядя", Class::Blood),
            true,
        ),
        ("зять — свойственник", all("зять", Class::InLaw), true),
        ("брат матери ⊑ дядя", le0("брат матери", "дядя"), true),
        (
            "брат матери = мать брата",
            eq0("брат матери", "мать брата"),
            false,
        ),
        (
            "мать брата = мать после свёртки по умолчанию",
            folded("мать брата") == get("мать").level0(),
            true,
        ),
        ("тесть = свёкор на уровне 0", eq0("тесть", "свёкор"), false),
        ("тесть = свёкор на уровне 1", eq1("тесть", "свёкор"), true),
        ("тесть ⊑ father-in-law", le0("тесть", "father-in-law"), true),
        (
            "father-in-law = тесть ∪ свёкор на уровне 1",
            get("father-in-law").level1() == union1("тесть", "свёкор"),
            true,
        ),
        (
            "father-in-law = тесть ∪ свёкор на уровне 0",
            get("father-in-law").level0() == union0("тесть", "свёкор"),
            true,
        ),
        ("uncle = дядя", eq0("uncle", "дядя"), true),
        ("avunculus ⊑ дядя", le0("avunculus", "дядя"), true),
        ("дядя ⊑ avunculus", le0("дядя", "avunculus"), false),
        (
            "patruus ∪ avunculus = дядя (кровный)",
            union0("patruus", "avunculus") == get("дядя (кровный)").level0(),
            true,
        ),
        (
            "avunculus = брат матери",
            eq0("avunculus", "брат матери"),
            true,
        ),
        (
            "двоюродный брат ⊑ cousin",
            le0("двоюродный брат", "cousin"),
            true,
        ),
        (
            "cousin ⊑ двоюродный брат",
            le0("cousin", "двоюродный брат"),
            false,
        ),
        (
            "общее у дяди и тёти: Px Px Cx + Px Px Cx Sx",
            common(get("дядя"), get("тётя")) == "Px Px Cx + Px Px Cx Sx",
            true,
        ),
    ];
    println!("\n# Вопросы\n");
    for (q, got, want) in &questions {
        let mark = if got == want { "ок" } else { "НЕ ТАК" };
        if got != want {
            bad += 1;
        }
        println!("{mark:<6} {q}: {}", if *got { "да" } else { "нет" });
    }
    println!(
        "\nОбщее у дяди и тёти: {}.",
        common(get("дядя"), get("тётя"))
    );
    println!(
        "Общее у тестя и свёкра: {}.",
        common(get("тесть"), get("свёкор"))
    );

    if bad == 0 {
        println!("\nВсё сходится.");
        ExitCode::SUCCESS
    } else {
        println!("\nРасхождений: {bad}.");
        ExitCode::FAILURE
    }
}
