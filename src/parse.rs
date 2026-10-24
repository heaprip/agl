//! Line-based parser of the case notation.
//!
//! ```text
//! axis NAME
//! value AXIS VALUE [in PARENT]
//! overlap AXIS A B
//! normative_axis AXIS
//! normative PRED
//! relation PRED(role, role, ...)
//! gap PRED KIND [resolved_by AXIS]
//! plane NAME = SPEC
//! fact ID: LITERAL @ SPEC [STATUS]
//! rule ID strict|defeasible @ SPEC: LITERAL <- LIT, LIT, ...
//! defeats WINNER LOSER
//! query LITERAL @ SPEC [expect yes|no|unknown|conflict|gap]
//! concept NAME(role: ?v, ...) @ SPEC: ATOM, ..., ?a != ?b
//! word LANG WORD = CONCEPT
//! cover REL(role) | REL(role) ...
//! compare NAME @ SPEC vs NAME @ SPEC [expect same|below|above|apart|not_below|unknown]
//! ```
//!
//! SPEC is `item + item ...`, where an item is a plane name or `axis:value`.
//! A statement continues on the next line while it ends with `,` or `<-`.

use crate::model::*;
use crate::units::{Dim, Units};

/// Reads a file, expanding `include PATH` lines (relative to the including
/// file) in place, and parses the result. Line numbers in errors refer to the
/// expanded text.
pub fn parse_file(path: &std::path::Path) -> Result<Program, String> {
    let mut stack = Vec::new();
    let src = expand(path, &mut stack)?;
    parse(&src)
}

fn expand(path: &std::path::Path, stack: &mut Vec<std::path::PathBuf>) -> Result<String, String> {
    let canon = path
        .canonicalize()
        .map_err(|e| format!("{}: {e}", path.display()))?;
    if stack.contains(&canon) {
        return Err(format!("include cycle through {}", path.display()));
    }
    stack.push(canon);
    let src = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let dir = path.parent().unwrap_or_else(|| std::path::Path::new("."));
    let mut out = String::new();
    for line in src.lines() {
        match line.trim().strip_prefix("include ") {
            Some(rel) => out.push_str(&expand(&dir.join(rel.trim()), stack)?),
            None => {
                out.push_str(line);
                out.push('\n');
            }
        }
    }
    stack.pop();
    Ok(out)
}

pub fn parse(src: &str) -> Result<Program, String> {
    let mut prog = Program::default();
    let stmts = statements(src);
    // Units first: numbers anywhere in the program may use them.
    let (mut quantities, mut units) = (Vec::new(), Vec::new());
    for (line_no, stmt) in &stmts {
        let (kw, rest) = stmt.split_once(char::is_whitespace).unwrap_or((stmt, ""));
        let err = |m: &str| format!("line {line_no}: {m}");
        match kw {
            "quantity" => match rest.split_whitespace().collect::<Vec<_>>().as_slice() {
                [q, sym] => quantities.push((ident(q)?.to_string(), sym.to_string())),
                _ => return Err(err("expected `quantity NAME UNIT`")),
            },
            "unit" => match rest.split_once('=') {
                Some((sym, def)) if !sym.trim().is_empty() => {
                    units.push((sym.trim().to_string(), def.trim().to_string()))
                }
                _ => return Err(err("expected `unit SYMBOL = [SCALE] UNIT`")),
            },
            _ => {}
        }
    }
    let u = Units::declare(&quantities, &units)?;
    for (line_no, stmt) in stmts {
        let (nf, nr, nq, nu, nb) = (
            prog.facts.len(),
            prog.rules.len(),
            prog.queries.len(),
            prog.uniques.len(),
            prog.forbids.len(),
        );
        let (nc, nw, nm) = (prog.concepts.len(), prog.words.len(), prog.compares.len());
        parse_statement(&mut prog, &u, &stmt).map_err(|e| format!("line {line_no}: {e}"))?;
        prog.facts[nf..].iter_mut().for_each(|f| f.line = line_no);
        prog.rules[nr..].iter_mut().for_each(|r| r.line = line_no);
        prog.queries[nq..].iter_mut().for_each(|q| q.line = line_no);
        prog.uniques[nu..].iter_mut().for_each(|u| u.line = line_no);
        prog.forbids[nb..].iter_mut().for_each(|b| b.line = line_no);
        prog.concepts[nc..]
            .iter_mut()
            .for_each(|c| c.line = line_no);
        prog.words[nw..].iter_mut().for_each(|w| w.line = line_no);
        prog.compares[nm..]
            .iter_mut()
            .for_each(|c| c.line = line_no);
    }
    compile_concepts(&mut prog);
    prog.units = u;
    Ok(prog)
}

/// Each sense of a concept becomes a strict rule, so the kernel recognizes the
/// concept in data. Rule ids number the senses of a name in the canonical order
/// of their definitions, not in the order of statements or of body literals.
fn compile_concepts(prog: &mut Program) {
    let mut senses: Vec<(String, String, Rule)> = prog
        .concepts
        .iter()
        .map(|c| {
            let rule = Rule {
                id: String::new(),
                head: c.head.clone(),
                body: c.body.clone(),
                strength: Strength::Strict,
                plane: c.plane.clone(),
                line: c.line,
            };
            (c.head.rel.clone(), crate::concept::sense_key(c), rule)
        })
        .collect();
    senses.sort_by(|a, b| (&a.0, &a.1).cmp(&(&b.0, &b.1)));
    let mut k = 0;
    for i in 0..senses.len() {
        k = if i > 0 && senses[i - 1].0 == senses[i].0 {
            k + 1
        } else {
            1
        };
        let (name, _, mut rule) = senses[i].clone();
        rule.id = format!("{name}.{k}");
        prog.rules.push(rule);
    }
}

fn statements(src: &str) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    let mut buf = String::new();
    let mut start = 0;
    for (i, raw) in src.lines().enumerate() {
        let line = match raw.find('#') {
            Some(p) => &raw[..p],
            None => raw,
        }
        .trim();
        if line.is_empty() && buf.is_empty() {
            continue;
        }
        if buf.is_empty() {
            start = i + 1;
        } else {
            buf.push(' ');
        }
        buf.push_str(line);
        if !(buf.ends_with(',') || buf.ends_with("<-")) {
            out.push((start, std::mem::take(&mut buf)));
        }
    }
    if !buf.is_empty() {
        out.push((start, buf));
    }
    out
}

fn parse_statement(prog: &mut Program, u: &Units, stmt: &str) -> Result<(), String> {
    let (kw, rest) = stmt.split_once(char::is_whitespace).unwrap_or((stmt, ""));
    let rest = rest.trim();
    match kw {
        "quantity" | "unit" => {}
        "axis" => prog.axes.declare_axis(ident(rest)?),
        "value" => {
            let parts: Vec<&str> = rest.split_whitespace().collect();
            match parts.as_slice() {
                [axis, value] => prog.axes.declare_value(axis, value, None)?,
                [axis, value, "in", parent] => {
                    prog.axes.declare_value(axis, value, Some(parent))?
                }
                _ => return Err("expected `value AXIS VALUE [in PARENT]`".into()),
            }
        }
        "overlap" => {
            let parts: Vec<&str> = rest.split_whitespace().collect();
            let [axis, a, b] = parts.as_slice() else {
                return Err("expected `overlap AXIS A B`".into());
            };
            prog.axes.declare_overlap(axis, a, b)?;
        }
        "normative_axis" => {
            prog.normative_axes.insert(ident(rest)?.to_string());
        }
        "normative" => {
            prog.normative_preds.insert(ident(rest)?.to_string());
        }
        "relation" => {
            let (name, roles) = rest
                .split_once('(')
                .ok_or("expected `relation PRED(role, ...)`")?;
            let roles = roles.strip_suffix(')').ok_or("missing `)`")?;
            let roles: Vec<String> = roles
                .split(',')
                .map(|r| r.trim().to_string())
                .filter(|r| !r.is_empty())
                .collect();
            prog.relations
                .insert(ident(name.trim())?.to_string(), roles);
        }
        "gap" => {
            let parts: Vec<&str> = rest.split_whitespace().collect();
            let (pred, gap) = match parts.as_slice() {
                [pred, kind] => (
                    pred,
                    Gap {
                        kind: kind.to_string(),
                        resolved_by: None,
                    },
                ),
                [pred, kind, "resolved_by", axis] => (
                    pred,
                    Gap {
                        kind: kind.to_string(),
                        resolved_by: Some(axis.to_string()),
                    },
                ),
                _ => return Err("expected `gap PRED KIND [resolved_by AXIS]`".into()),
            };
            prog.gaps.insert(pred.to_string(), gap);
        }
        "plane" => {
            let (name, spec) = rest.split_once('=').ok_or("expected `plane NAME = SPEC`")?;
            let plane = parse_spec(prog, spec.trim())?;
            prog.planes.insert(ident(name.trim())?.to_string(), plane);
        }
        "fact" => {
            let (id, body) = rest
                .split_once(':')
                .ok_or("expected `fact ID: LITERAL @ SPEC`")?;
            let (lit, spec) = split_at_plane(body)?;
            let (spec, status) = match spec.rfind('[') {
                Some(p) => (
                    spec[..p].trim(),
                    spec[p + 1..].trim_end_matches(']').trim().to_string(),
                ),
                None => (spec, "given".to_string()),
            };
            let atom = parse_atom_in(lit.trim(), u)?;
            let plane = parse_spec(prog, spec)?;
            prog.facts.push(Fact {
                id: ident(id.trim())?.to_string(),
                atom,
                plane,
                status,
                line: 0,
            });
        }
        "rule" => {
            let (head_part, body) = rest.split_once("<-").ok_or("expected `<-` in rule")?;
            let (decl, head) = split_rule_head(head_part)?;
            let (decl, spec) = split_at_plane(decl)?;
            let mut words = decl.split_whitespace();
            let id = words.next().ok_or("missing rule id")?;
            let strength = match words.next() {
                Some("strict") => Strength::Strict,
                Some("defeasible") => Strength::Defeasible,
                other => return Err(format!("expected `strict` or `defeasible`, got {other:?}")),
            };
            let head = parse_atom_in(head.trim(), u)?;
            let body = split_top(body, ',')
                .into_iter()
                .map(|l| parse_lit(l.trim(), u))
                .collect::<Result<Vec<_>, _>>()?;
            let plane = parse_spec(prog, spec)?;
            prog.rules.push(Rule {
                id: ident(id)?.to_string(),
                head,
                body,
                strength,
                plane,
                line: 0,
            });
        }
        "status" => {
            let names: Vec<&str> = rest.split('>').map(str::trim).collect();
            if names.iter().any(|n| ident(n).is_err()) || names.len() < 2 {
                return Err("expected `status A > B > ...`".into());
            }
            let n = names.len();
            for (i, name) in names.into_iter().enumerate() {
                prog.status_rank.insert(name.to_string(), n - i);
            }
        }
        "forbid" => {
            let (lit, spec) = split_at_plane(rest)?;
            let atom = parse_atom_in(lit.trim(), u)?;
            let plane = parse_spec(prog, spec)?;
            prog.forbids.push(Forbid {
                atom,
                plane,
                line: 0,
            });
        }
        "unique" => {
            let (head, by) = rest
                .split_once(" by ")
                .ok_or("expected `unique REL(role) by (keys)`")?;
            let atom = parse_role_list(head)?;
            let keys = by
                .trim()
                .strip_prefix('(')
                .and_then(|b| b.strip_suffix(')'))
                .ok_or("expected `by (keys)`")?;
            let by: Vec<String> = keys
                .split(',')
                .map(|k| k.trim().to_string())
                .filter(|k| !k.is_empty())
                .collect();
            let [role] = atom.1.as_slice() else {
                return Err("`unique` names exactly one role".into());
            };
            prog.uniques.push(Unique {
                rel: atom.0,
                role: role.clone(),
                by,
                line: 0,
            });
        }
        "defeats" => {
            let parts: Vec<&str> = rest.split_whitespace().collect();
            let [w, l] = parts.as_slice() else {
                return Err("expected `defeats WINNER LOSER`".into());
            };
            prog.defeats.insert((w.to_string(), l.to_string()));
        }
        "query" => {
            let (lit, spec) = split_at_plane(rest)?;
            let mut words: Vec<&str> = spec.split_whitespace().collect();
            let heldout = words.last() == Some(&"heldout");
            if heldout {
                words.pop();
            }
            let expect = match words.iter().position(|w| *w == "expect") {
                Some(k) => {
                    let v = parse_verdict(words.get(k + 1).copied().unwrap_or(""))?;
                    words.truncate(k);
                    Some(v)
                }
                None => None,
            };
            let situate = match words.iter().position(|w| *w == "situate") {
                Some(k) => {
                    let ctx = words
                        .get(k + 1)
                        .copied()
                        .ok_or("expected `situate CONTEXT`")?;
                    let ctx = ident(ctx)?.to_string();
                    words.truncate(k);
                    Some(ctx)
                }
                None => None,
            };
            let spec = words.join(" ");
            let spec = spec.as_str();
            let atom = parse_atom_in(lit.trim(), u)?;
            let plane = parse_spec(prog, spec)?;
            prog.queries.push(Query {
                atom,
                plane,
                situate,
                expect,
                heldout,
                line: 0,
            });
        }
        "concept" => {
            let (head_part, body) = split_rule_head(rest)?;
            let (head, spec) = split_at_plane(head_part)?;
            let head = parse_atom_in(head, u)?;
            if head.neg {
                return Err("a concept head is positive".into());
            }
            let mut seen = Vec::new();
            for (_, t) in &head.args {
                match t {
                    Term::Var(v) if !seen.contains(v) => seen.push(v.clone()),
                    _ => return Err("concept roles take distinct variables".into()),
                }
            }
            let body = split_top(body, ',')
                .into_iter()
                .map(|l| parse_lit(l.trim(), u))
                .collect::<Result<Vec<_>, _>>()?;
            for lit in &body {
                let ok = match lit {
                    Lit::Atom(a) => {
                        !a.neg && a.args.iter().all(|(_, t)| !matches!(t, Term::Num(..)))
                    }
                    Lit::Cmp(Expr::Term(Term::Var(_)), CmpOp::Ne, Expr::Term(Term::Var(_))) => true,
                    _ => false,
                };
                if !ok {
                    return Err(format!(
                        "a concept body takes positive atoms without numbers and `?a != ?b`, not `{lit}`"
                    ));
                }
            }
            let plane = parse_spec(prog, spec)?;
            prog.concepts.push(Concept {
                head,
                body,
                plane,
                line: 0,
            });
        }
        "cover" => {
            let mut alts = Vec::new();
            for alt in rest.split('|') {
                let (rel, roles) = parse_role_list(alt)?;
                let [role] = roles.as_slice() else {
                    return Err("`cover` alternatives name exactly one role".into());
                };
                alts.push((rel, role.clone()));
            }
            if alts.len() < 2 {
                return Err("expected `cover REL(role) | REL(role) ...`".into());
            }
            prog.covers.push(alts);
        }
        "word" => {
            let (left, concept) = rest
                .split_once('=')
                .ok_or("expected `word LANG WORD = CONCEPT`")?;
            let parts: Vec<&str> = left.split_whitespace().collect();
            let [lang, word] = parts.as_slice() else {
                return Err("expected `word LANG WORD = CONCEPT`".into());
            };
            prog.words.push(Word {
                lang: ident(lang)?.to_string(),
                word: ident(word)?.to_string(),
                concept: ident(concept.trim())?.to_string(),
                line: 0,
            });
        }
        "compare" => {
            let (left, right) = rest
                .split_once(" vs ")
                .ok_or("expected `compare NAME @ SPEC vs NAME @ SPEC`")?;
            let mut right = right.trim();
            let mut expect = None;
            if let Some((r, e)) = right.split_once(" expect ") {
                expect = Some(match e.trim() {
                    "same" => Relation::Same,
                    "below" => Relation::Below,
                    "above" => Relation::Above,
                    "apart" => Relation::Apart,
                    "not_below" => Relation::NotBelow,
                    "unknown" => Relation::Unknown,
                    other => return Err(format!("unknown relation `{other}`")),
                });
                right = r.trim();
            }
            let side = |s: &str| -> Result<(String, Plane), String> {
                let (name, spec) = split_at_plane(s)?;
                Ok((ident(name)?.to_string(), parse_spec(prog, spec)?))
            };
            let (left, right) = (side(left)?, side(right)?);
            prog.compares.push(Compare {
                left,
                right,
                expect,
                line: 0,
            });
        }
        other => return Err(format!("unknown statement `{other}`")),
    }
    Ok(())
}

/// `NAME(a, b, ...)` with bare role names.
fn parse_role_list(s: &str) -> Result<(String, Vec<String>), String> {
    let (name, roles) = s.trim().split_once('(').ok_or("expected `NAME(roles)`")?;
    let roles = roles.strip_suffix(')').ok_or("missing `)`")?;
    let roles = roles
        .split(',')
        .map(|r| r.trim().to_string())
        .filter(|r| !r.is_empty())
        .collect();
    Ok((ident(name.trim())?.to_string(), roles))
}

fn parse_verdict(s: &str) -> Result<Verdict, String> {
    Ok(match s {
        "yes" => Verdict::Yes,
        "no" => Verdict::No,
        "unknown" => Verdict::Unknown,
        "conflict" => Verdict::Conflict,
        "gap" => Verdict::Gap,
        _ => return Err(format!("unknown verdict `{s}`")),
    })
}

fn ident(s: &str) -> Result<&str, String> {
    let ok = !s.is_empty()
        && s.chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '-' || c == '.');
    if ok {
        Ok(s)
    } else {
        Err(format!("bad identifier `{s}`"))
    }
}

/// Splits `ID strength @ SPEC: HEAD` at the colon that ends the plane spec.
/// The spec has no parentheses, and the head starts with `rel(`.
fn split_rule_head(s: &str) -> Result<(&str, &str), String> {
    let at = s.find('@').ok_or("expected `@ PLANE` in rule")?;
    for (p, _) in s.match_indices(':').filter(|(p, _)| *p > at) {
        if !s[at..p].contains('(') && is_atom_syntax(s[p + 1..].trim()) {
            return Ok((&s[..p], &s[p + 1..]));
        }
    }
    Err("expected `: HEAD` after the rule plane".into())
}

fn split_at_plane(s: &str) -> Result<(&str, &str), String> {
    let p = s.rfind('@').ok_or("expected `@ PLANE`")?;
    Ok((s[..p].trim(), s[p + 1..].trim()))
}

fn parse_spec(prog: &Program, spec: &str) -> Result<Plane, String> {
    let mut plane = Plane::new();
    for item in spec.split('+').map(str::trim).filter(|s| !s.is_empty()) {
        let part = if let Some((axis, value)) = item.split_once(':') {
            let (axis, value) = (axis.trim(), value.trim());
            if !prog.axes.has_value(axis, value) {
                return Err(format!("undeclared value `{axis}:{value}`"));
            }
            Plane::from([(axis.to_string(), value.to_string())])
        } else {
            prog.planes
                .get(item)
                .cloned()
                .ok_or_else(|| format!("unknown plane `{item}`"))?
        };
        plane = prog.axes.plane_meet(&plane, &part).ok_or_else(|| {
            format!("plane `{spec}` is empty: `{item}` is disjoint from the rest")
        })?;
    }
    Ok(plane)
}

fn split_top(s: &str, sep: char) -> Vec<&str> {
    let mut out = Vec::new();
    let (mut depth, mut start) = (0i32, 0);
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            c if c == sep && depth == 0 => {
                out.push(&s[start..i]);
                start = i + c.len_utf8();
            }
            _ => {}
        }
    }
    out.push(&s[start..]);
    out.into_iter().filter(|x| !x.trim().is_empty()).collect()
}

fn is_atom_syntax(s: &str) -> bool {
    let s = s
        .strip_prefix('¬')
        .or_else(|| s.strip_prefix('~'))
        .unwrap_or(s)
        .trim_start();
    let name_len = s
        .chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_')
        .map(char::len_utf8)
        .sum::<usize>();
    name_len > 0 && s[name_len..].starts_with('(')
}

fn parse_lit(s: &str, u: &Units) -> Result<Lit, String> {
    if is_atom_syntax(s) {
        return Ok(Lit::Atom(parse_atom_in(s, u)?));
    }
    if let Some(agg) = parse_agg(s, u)? {
        return Ok(agg);
    }
    for (tok, op) in [
        ("<=", CmpOp::Le),
        (">=", CmpOp::Ge),
        ("!=", CmpOp::Ne),
        ("<", CmpOp::Lt),
        (">", CmpOp::Gt),
        ("=", CmpOp::Eq),
    ] {
        if let Some(p) = s.find(tok) {
            let l = parse_expr(&s[..p], u)?;
            let r = parse_expr(&s[p + tok.len()..], u)?;
            return Ok(Lit::Cmp(l, op, r));
        }
    }
    Err(format!("cannot read literal `{s}`"))
}

/// `?v = sum(EXPR) over (ATOM, ATOM)`; also `count`, `min`, `max`.
fn parse_agg(s: &str, u: &Units) -> Result<Option<Lit>, String> {
    let Some((lhs, rhs)) = s.split_once('=') else {
        return Ok(None);
    };
    let rhs = rhs.trim_start();
    let func = [
        ("sum(", AggFn::Sum),
        ("count(", AggFn::Count),
        ("min(", AggFn::Min),
        ("max(", AggFn::Max),
    ]
    .into_iter()
    .find(|(p, _)| rhs.starts_with(p));
    let Some((prefix, func)) = func else {
        return Ok(None);
    };
    let var = lhs
        .trim()
        .strip_prefix('?')
        .ok_or("aggregate must bind a variable: `?v = sum(...) over (...)`")?;
    let inner_start = prefix.len();
    let mut depth = 1;
    let mut end = None;
    for (i, c) in rhs[inner_start..].char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    end = Some(inner_start + i);
                    break;
                }
            }
            _ => {}
        }
    }
    let end = end.ok_or("unbalanced parentheses in aggregate")?;
    let expr = parse_expr(&rhs[inner_start..end], u)?;
    let rest = rhs[end + 1..].trim_start();
    let list = rest
        .strip_prefix("over")
        .ok_or("expected `over (ATOMS)` after the aggregate")?
        .trim();
    let list = list
        .strip_prefix('(')
        .and_then(|l| l.strip_suffix(')'))
        .ok_or("expected `over (ATOMS)`")?;
    let over = split_top(list, ',')
        .into_iter()
        .map(|a| parse_atom_in(a.trim(), u))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Some(Lit::Agg {
        var: ident(var)?.to_string(),
        func,
        expr,
        over,
    }))
}

/// An atom with numbers in plain form only; `parse_atom_in` reads units.
pub fn parse_atom(s: &str) -> Result<Atom, String> {
    parse_atom_in(s, &Units::default())
}

pub fn parse_atom_in(s: &str, u: &Units) -> Result<Atom, String> {
    let (neg, s) = match s.strip_prefix('¬').or_else(|| s.strip_prefix('~')) {
        Some(rest) => (true, rest.trim_start()),
        None => (false, s),
    };
    let (rel, args) = s
        .split_once('(')
        .ok_or_else(|| format!("expected `rel(...)` in `{s}`"))?;
    let args = args
        .trim_end()
        .strip_suffix(')')
        .ok_or_else(|| format!("missing `)` in `{s}`"))?;
    let mut out = Vec::new();
    for arg in split_top(args, ',') {
        let (role, term) = arg
            .split_once(':')
            .ok_or_else(|| format!("expected `role: term` in `{arg}`"))?;
        out.push((ident(role.trim())?.to_string(), parse_term(term.trim(), u)?));
    }
    Ok(Atom::new(ident(rel.trim())?.to_string(), out, neg))
}

fn parse_term(s: &str, u: &Units) -> Result<Term, String> {
    if let Some(v) = s.strip_prefix('?') {
        return Ok(Term::Var(ident(v)?.to_string()));
    }
    if let Some((num, unit)) = s.split_once('[') {
        let n: f64 = num
            .trim()
            .parse()
            .map_err(|_| format!("bad number `{num}`"))?;
        let unit = unit
            .strip_suffix(']')
            .ok_or_else(|| format!("missing `]` in `{s}`"))?;
        let (scale, dim) = u.parse_unit(unit)?;
        return Ok(Term::Num(n * scale, dim));
    }
    if let Ok(n) = s.parse::<f64>() {
        return Ok(Term::Num(n, Dim::NONE));
    }
    Ok(Term::Sym(ident(s)?.to_string()))
}

fn parse_expr(s: &str, u: &Units) -> Result<Expr, String> {
    let tokens = tokenize(s)?;
    let mut pos = 0;
    let e = expr(&tokens, &mut pos, u)?;
    if pos != tokens.len() {
        return Err(format!("trailing input in expression `{s}`"));
    }
    Ok(e)
}

fn tokenize(s: &str) -> Result<Vec<String>, String> {
    let mut out = Vec::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if "+-*/^()".contains(c) {
            out.push(c.to_string());
            i += 1;
        } else {
            let start = i;
            while i < chars.len() {
                let ch = chars[i];
                let exp_sign = (ch == '-' || ch == '+')
                    && i > start
                    && (chars[i - 1] == 'e' || chars[i - 1] == 'E')
                    && chars[start].is_ascii_digit();
                if ch.is_alphanumeric() || ch == '_' || ch == '.' || ch == '?' || exp_sign {
                    i += 1;
                } else {
                    break;
                }
            }
            if i == start {
                return Err(format!("unexpected `{c}` in expression"));
            }
            // A unit in brackets belongs to the number before it: `9.81[m/s^2]`.
            if i < chars.len() && chars[i] == '[' {
                while i < chars.len() && chars[i] != ']' {
                    i += 1;
                }
                i += 1;
            }
            out.push(chars[start..i.min(chars.len())].iter().collect());
        }
    }
    Ok(out)
}

fn expr(t: &[String], pos: &mut usize, u: &Units) -> Result<Expr, String> {
    let mut lhs = term(t, pos, u)?;
    while *pos < t.len() && (t[*pos] == "+" || t[*pos] == "-") {
        let op = t[*pos].chars().next().unwrap();
        *pos += 1;
        lhs = Expr::Bin(Box::new(lhs), op, Box::new(term(t, pos, u)?));
    }
    Ok(lhs)
}

fn term(t: &[String], pos: &mut usize, u: &Units) -> Result<Expr, String> {
    let mut lhs = factor(t, pos, u)?;
    while *pos < t.len() && (t[*pos] == "*" || t[*pos] == "/") {
        let op = t[*pos].chars().next().unwrap();
        *pos += 1;
        lhs = Expr::Bin(Box::new(lhs), op, Box::new(factor(t, pos, u)?));
    }
    Ok(lhs)
}

fn factor(t: &[String], pos: &mut usize, u: &Units) -> Result<Expr, String> {
    let base = primary(t, pos, u)?;
    if *pos < t.len() && t[*pos] == "^" {
        *pos += 1;
        return Ok(Expr::Bin(Box::new(base), '^', Box::new(factor(t, pos, u)?)));
    }
    Ok(base)
}

fn primary(t: &[String], pos: &mut usize, u: &Units) -> Result<Expr, String> {
    let tok = t.get(*pos).ok_or("unexpected end of expression")?;
    *pos += 1;
    match tok.as_str() {
        "(" => {
            let e = expr(t, pos, u)?;
            if t.get(*pos).map(String::as_str) != Some(")") {
                return Err("missing `)` in expression".into());
            }
            *pos += 1;
            Ok(e)
        }
        "-" => Ok(Expr::Bin(
            Box::new(Expr::Term(Term::Num(0.0, Dim::NONE))),
            '-',
            Box::new(primary(t, pos, u)?),
        )),
        _ => Ok(Expr::Term(parse_term(tok, u)?)),
    }
}
