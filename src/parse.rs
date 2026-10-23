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
//! ```
//!
//! SPEC is `item + item ...`, where an item is a plane name or `axis:value`.
//! A statement continues on the next line while it ends with `,` or `<-`.

use crate::model::*;

pub fn parse(src: &str) -> Result<Program, String> {
    let mut prog = Program::default();
    for (line_no, stmt) in statements(src) {
        let (nf, nr, nq) = (prog.facts.len(), prog.rules.len(), prog.queries.len());
        parse_statement(&mut prog, &stmt).map_err(|e| format!("line {line_no}: {e}"))?;
        prog.facts[nf..].iter_mut().for_each(|f| f.line = line_no);
        prog.rules[nr..].iter_mut().for_each(|r| r.line = line_no);
        prog.queries[nq..].iter_mut().for_each(|q| q.line = line_no);
    }
    Ok(prog)
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

fn parse_statement(prog: &mut Program, stmt: &str) -> Result<(), String> {
    let (kw, rest) = stmt.split_once(char::is_whitespace).unwrap_or((stmt, ""));
    let rest = rest.trim();
    match kw {
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
            let atom = parse_atom(lit.trim())?;
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
            let head = parse_atom(head.trim())?;
            let body = split_top(body, ',')
                .into_iter()
                .map(|l| parse_lit(l.trim()))
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
        "defeats" => {
            let parts: Vec<&str> = rest.split_whitespace().collect();
            let [w, l] = parts.as_slice() else {
                return Err("expected `defeats WINNER LOSER`".into());
            };
            prog.defeats.insert((w.to_string(), l.to_string()));
        }
        "query" => {
            let (lit, spec) = split_at_plane(rest)?;
            let (spec, expect) = match spec.split_once(" expect ") {
                Some((s, e)) => (s.trim(), Some(parse_verdict(e.trim())?)),
                None => (spec.trim(), None),
            };
            let atom = parse_atom(lit.trim())?;
            let plane = parse_spec(prog, spec)?;
            prog.queries.push(Query {
                atom,
                plane,
                expect,
                line: 0,
            });
        }
        other => return Err(format!("unknown statement `{other}`")),
    }
    Ok(())
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

fn parse_lit(s: &str) -> Result<Lit, String> {
    if is_atom_syntax(s) {
        return Ok(Lit::Atom(parse_atom(s)?));
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
            let l = parse_expr(&s[..p])?;
            let r = parse_expr(&s[p + tok.len()..])?;
            return Ok(Lit::Cmp(l, op, r));
        }
    }
    Err(format!("cannot read literal `{s}`"))
}

pub fn parse_atom(s: &str) -> Result<Atom, String> {
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
        out.push((ident(role.trim())?.to_string(), parse_term(term.trim())?));
    }
    Ok(Atom::new(ident(rel.trim())?.to_string(), out, neg))
}

fn parse_term(s: &str) -> Result<Term, String> {
    if let Some(v) = s.strip_prefix('?') {
        return Ok(Term::Var(ident(v)?.to_string()));
    }
    if let Ok(n) = s.parse::<f64>() {
        return Ok(Term::Num(n));
    }
    Ok(Term::Sym(ident(s)?.to_string()))
}

fn parse_expr(s: &str) -> Result<Expr, String> {
    let tokens = tokenize(s)?;
    let mut pos = 0;
    let e = expr(&tokens, &mut pos)?;
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
            out.push(chars[start..i].iter().collect());
        }
    }
    Ok(out)
}

fn expr(t: &[String], pos: &mut usize) -> Result<Expr, String> {
    let mut lhs = term(t, pos)?;
    while *pos < t.len() && (t[*pos] == "+" || t[*pos] == "-") {
        let op = t[*pos].chars().next().unwrap();
        *pos += 1;
        lhs = Expr::Bin(Box::new(lhs), op, Box::new(term(t, pos)?));
    }
    Ok(lhs)
}

fn term(t: &[String], pos: &mut usize) -> Result<Expr, String> {
    let mut lhs = factor(t, pos)?;
    while *pos < t.len() && (t[*pos] == "*" || t[*pos] == "/") {
        let op = t[*pos].chars().next().unwrap();
        *pos += 1;
        lhs = Expr::Bin(Box::new(lhs), op, Box::new(factor(t, pos)?));
    }
    Ok(lhs)
}

fn factor(t: &[String], pos: &mut usize) -> Result<Expr, String> {
    let base = primary(t, pos)?;
    if *pos < t.len() && t[*pos] == "^" {
        *pos += 1;
        return Ok(Expr::Bin(Box::new(base), '^', Box::new(factor(t, pos)?)));
    }
    Ok(base)
}

fn primary(t: &[String], pos: &mut usize) -> Result<Expr, String> {
    let tok = t.get(*pos).ok_or("unexpected end of expression")?;
    *pos += 1;
    match tok.as_str() {
        "(" => {
            let e = expr(t, pos)?;
            if t.get(*pos).map(String::as_str) != Some(")") {
                return Err("missing `)` in expression".into());
            }
            *pos += 1;
            Ok(e)
        }
        "-" => Ok(Expr::Bin(
            Box::new(Expr::Term(Term::Num(0.0))),
            '-',
            Box::new(primary(t, pos)?),
        )),
        _ => Ok(Expr::Term(parse_term(tok)?)),
    }
}
