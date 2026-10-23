//! Physical dimensions: exponents over the seven SI base units, and a small
//! table of named units with their scale to SI. Values are stored in SI.

use std::fmt;

/// Exponents of m, kg, s, A, K, mol, cd.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Dim(pub [i8; 7]);

const BASE: [&str; 7] = ["m", "kg", "s", "A", "K", "mol", "cd"];

impl Dim {
    pub const NONE: Dim = Dim([0; 7]);

    pub fn is_none(&self) -> bool {
        *self == Dim::NONE
    }

    pub fn times(self, o: Dim) -> Dim {
        let mut d = self.0;
        d.iter_mut().zip(o.0).for_each(|(a, b)| *a += b);
        Dim(d)
    }

    pub fn per(self, o: Dim) -> Dim {
        let mut d = self.0;
        d.iter_mut().zip(o.0).for_each(|(a, b)| *a -= b);
        Dim(d)
    }

    pub fn pow(self, n: i32) -> Option<Dim> {
        let mut d = self.0;
        for a in &mut d {
            *a = i8::try_from(i32::from(*a) * n).ok()?;
        }
        Some(Dim(d))
    }
}

impl fmt::Display for Dim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let parts: Vec<String> = BASE
            .iter()
            .zip(self.0)
            .filter(|(_, e)| *e != 0)
            .map(|(u, e)| {
                if e == 1 {
                    u.to_string()
                } else {
                    format!("{u}^{e}")
                }
            })
            .collect();
        write!(f, "{}", parts.join(" "))
    }
}

fn d(m: i8, kg: i8, s: i8, a: i8, k: i8, mol: i8) -> Dim {
    Dim([m, kg, s, a, k, mol, 0])
}

/// Named units: symbol, scale to SI, dimension.
fn unit(sym: &str) -> Option<(f64, Dim)> {
    Some(match sym {
        "m" => (1.0, d(1, 0, 0, 0, 0, 0)),
        "kg" => (1.0, d(0, 1, 0, 0, 0, 0)),
        "s" => (1.0, d(0, 0, 1, 0, 0, 0)),
        "A" => (1.0, d(0, 0, 0, 1, 0, 0)),
        "K" => (1.0, d(0, 0, 0, 0, 1, 0)),
        "mol" => (1.0, d(0, 0, 0, 0, 0, 1)),
        "cd" => (1.0, Dim([0, 0, 0, 0, 0, 0, 1])),
        "g" => (1e-3, d(0, 1, 0, 0, 0, 0)),
        "mg" => (1e-6, d(0, 1, 0, 0, 0, 0)),
        "km" => (1e3, d(1, 0, 0, 0, 0, 0)),
        "cm" => (1e-2, d(1, 0, 0, 0, 0, 0)),
        "mm" => (1e-3, d(1, 0, 0, 0, 0, 0)),
        "um" => (1e-6, d(1, 0, 0, 0, 0, 0)),
        "nm" => (1e-9, d(1, 0, 0, 0, 0, 0)),
        "L" => (1e-3, d(3, 0, 0, 0, 0, 0)),
        "mL" => (1e-6, d(3, 0, 0, 0, 0, 0)),
        "mmol" => (1e-3, d(0, 0, 0, 0, 0, 1)),
        "M" => (1e3, d(-3, 0, 0, 0, 0, 1)),
        "mM" => (1.0, d(-3, 0, 0, 0, 0, 1)),
        "min" => (60.0, d(0, 0, 1, 0, 0, 0)),
        "h" => (3600.0, d(0, 0, 1, 0, 0, 0)),
        "day" => (86400.0, d(0, 0, 1, 0, 0, 0)),
        "N" => (1.0, d(1, 1, -2, 0, 0, 0)),
        "J" => (1.0, d(2, 1, -2, 0, 0, 0)),
        "kJ" => (1e3, d(2, 1, -2, 0, 0, 0)),
        "W" => (1.0, d(2, 1, -3, 0, 0, 0)),
        "Pa" => (1.0, d(-1, 1, -2, 0, 0, 0)),
        "kPa" => (1e3, d(-1, 1, -2, 0, 0, 0)),
        "atm" => (101_325.0, d(-1, 1, -2, 0, 0, 0)),
        "mmHg" => (133.322_387_415, d(-1, 1, -2, 0, 0, 0)),
        _ => return None,
    })
}

/// Parses a unit expression such as `m/s^2`, `kJ/mol` or `kg m^2 s^-2`.
/// Juxtaposition and `*` multiply; every factor after `/` divides.
pub fn parse_unit(src: &str) -> Result<(f64, Dim), String> {
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
        let (sc, dm) = unit(sym).ok_or_else(|| format!("unknown unit `{sym}`"))?;
        let exp = if dividing { -exp } else { exp };
        scale *= sc.powi(exp);
        dim = dim.times(dm.pow(exp).ok_or("unit exponent overflow")?);
    }
    Ok((scale, dim))
}
