//! Dimensions and units, declared by the program (decision 23). The kernel
//! knows only the algebra: a dimension is a product of powers of base units,
//! and a unit is a scale times a dimension. Which quantities are basic and
//! what the units are called comes from the data:
//!
//! ```text
//! quantity length m
//! unit km = 1000 m
//! unit N = kg m/s^2
//! ```

use std::collections::BTreeMap;
use std::fmt;

/// Exponents of base units, by base unit symbol; zero exponents are absent.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Dim(BTreeMap<String, i8>);

impl Dim {
    pub const NONE: Dim = Dim(BTreeMap::new());

    pub fn base(sym: &str) -> Dim {
        Dim(BTreeMap::from([(sym.to_string(), 1)]))
    }

    pub fn is_none(&self) -> bool {
        self.0.is_empty()
    }

    fn combine(&self, o: &Dim, sign: i8) -> Option<Dim> {
        let mut d = self.0.clone();
        for (u, e) in &o.0 {
            let x = d.entry(u.clone()).or_insert(0);
            *x = x.checked_add(e.checked_mul(sign)?)?;
            if *x == 0 {
                d.remove(u);
            }
        }
        Some(Dim(d))
    }

    pub fn times(&self, o: &Dim) -> Option<Dim> {
        self.combine(o, 1)
    }

    pub fn per(&self, o: &Dim) -> Option<Dim> {
        self.combine(o, -1)
    }

    pub fn pow(&self, n: i32) -> Option<Dim> {
        let mut d = BTreeMap::new();
        for (u, e) in &self.0 {
            let x = i8::try_from(i32::from(*e) * n).ok()?;
            if x != 0 {
                d.insert(u.clone(), x);
            }
        }
        Some(Dim(d))
    }
}

impl fmt::Display for Dim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let parts: Vec<String> = self
            .0
            .iter()
            .map(|(u, e)| {
                if *e == 1 {
                    u.clone()
                } else {
                    format!("{u}^{e}")
                }
            })
            .collect();
        write!(f, "{}", parts.join(" "))
    }
}

/// Declared units: symbol → (scale to the base units, dimension).
#[derive(Clone, Debug, Default)]
pub struct Units {
    /// Base quantity → its base unit symbol.
    pub quantities: BTreeMap<String, String>,
    named: BTreeMap<String, (f64, Dim)>,
}

impl Units {
    /// Builds the table from `quantity NAME UNIT` and `unit SYM = [SCALE] EXPR`
    /// declarations, in any order: a unit may be defined through units
    /// declared after it.
    pub fn declare(
        quantities: &[(String, String)],
        units: &[(String, String)],
    ) -> Result<Units, String> {
        let mut t = Units::default();
        for (q, sym) in quantities {
            if let Some(old) = t.quantities.insert(q.clone(), sym.clone())
                && old != *sym
            {
                return Err(format!("quantity `{q}` declared with `{old}` and `{sym}`"));
            }
            t.add(sym, 1.0, Dim::base(sym))?;
        }
        let mut pending: Vec<&(String, String)> = units.iter().collect();
        while !pending.is_empty() {
            let before = pending.len();
            let mut still = Vec::new();
            for u in pending {
                match t.parse_definition(&u.1) {
                    Ok((scale, dim)) => t.add(&u.0, scale, dim)?,
                    Err(_) => still.push(u),
                }
            }
            if still.len() == before {
                let (sym, def) = still[0];
                let why = t.parse_definition(def).unwrap_err();
                return Err(format!("unit `{sym}`: {why}"));
            }
            pending = still;
        }
        Ok(t)
    }

    fn add(&mut self, sym: &str, scale: f64, dim: Dim) -> Result<(), String> {
        match self.named.get(sym) {
            Some(old) if *old != (scale, dim.clone()) => {
                Err(format!("unit `{sym}` declared twice differently"))
            }
            _ => {
                self.named.insert(sym.to_string(), (scale, dim));
                Ok(())
            }
        }
    }

    /// `1000 m`, `kg m/s^2`, `133.3 Pa`: an optional scale, then a unit.
    fn parse_definition(&self, src: &str) -> Result<(f64, Dim), String> {
        let src = src.trim();
        let (first, rest) = src.split_once(char::is_whitespace).unwrap_or((src, ""));
        let (n, unit) = match first.parse::<f64>() {
            Ok(n) => (n, rest),
            Err(_) => (1.0, src),
        };
        let (scale, dim) = self.parse_unit(unit)?;
        Ok((n * scale, dim))
    }

    /// Parses a unit expression such as `m/s^2`, `kJ/mol` or `kg m^2 s^-2`.
    /// Juxtaposition and `*` multiply; every factor after `/` divides.
    pub fn parse_unit(&self, src: &str) -> Result<(f64, Dim), String> {
        let mut scale = 1.0;
        let mut dim = Dim::NONE;
        let mut dividing = false;
        let spaced = src.replace('*', " ").replace('/', " / ");
        for tok in spaced.split_whitespace() {
            if tok == "/" {
                dividing = true;
                continue;
            }
            let (sym, exp) = match tok.split_once('^') {
                Some((s, e)) => (
                    s,
                    e.parse::<i32>()
                        .map_err(|_| format!("bad exponent in `{tok}`"))?,
                ),
                None => (tok, 1),
            };
            let (sc, dm) = self
                .named
                .get(sym)
                .ok_or_else(|| format!("unknown unit `{sym}`"))?;
            let exp = if dividing { -exp } else { exp };
            scale *= sc.powi(exp);
            dim = dim
                .times(&dm.pow(exp).ok_or("unit exponent overflow")?)
                .ok_or("unit exponent overflow")?;
        }
        Ok((scale, dim))
    }
}
