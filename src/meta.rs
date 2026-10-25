//! Common proof-relevant carrier shared by evaluators and relation builders.
//!
//! A claim is an OR node: it may have several pieces of evidence. Evidence is
//! an AND node: all premise claims are required. An entity is the stable
//! occurrence built by one intension; a projection says what that occurrence
//! denotes in one context. None of these IDs is derived from an extent alone.

use std::fmt;

use crate::model::{Plane, Strength, plane_to_string};

fn exact_key(namespace: &str, parts: impl IntoIterator<Item = impl AsRef<str>>) -> String {
    let mut out = format!("{}:{}", namespace.len(), namespace);
    for part in parts {
        let part = part.as_ref();
        out.push('|');
        out.push_str(&part.len().to_string());
        out.push(':');
        out.push_str(part);
    }
    out
}

macro_rules! stable_id {
    ($name:ident) => {
        #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(String);

        impl $name {
            pub fn named(namespace: &str, name: &str) -> Self {
                Self(exact_key(namespace, [name]))
            }

            pub fn derived(
                namespace: &str,
                parts: impl IntoIterator<Item = impl AsRef<str>>,
            ) -> Self {
                Self(exact_key(namespace, parts))
            }

            pub fn as_str(&self) -> &str {
                &self.0
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(&self.0)
            }
        }
    };
}

stable_id!(EntityId);
stable_id!(ClaimId);
stable_id!(EvidenceId);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PortBinding {
    pub role: String,
    pub target: EntityId,
}

impl PortBinding {
    pub fn new(role: impl Into<String>, target: EntityId) -> Self {
        Self {
            role: role.into(),
            target,
        }
    }
}

/// Immutable construction history. Domain-specific executors keep their
/// executable plan separately, but identity is made from this shared form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Intension {
    Primitive {
        source: String,
    },
    /// A rule or other operation applied to premise claims. Claims are used
    /// instead of one chosen proof so alternative evidence remains an OR.
    Derive {
        operation: String,
        premises: Vec<ClaimId>,
    },
    /// Structural composition of already first-class entities.
    Glue {
        operation: String,
        parts: Vec<EntityId>,
        wiring: Vec<(String, String)>,
        interface: Vec<String>,
    },
    /// A relation occurrence whose endpoints are themselves entities.
    Metaedge {
        relation: EntityId,
        ports: Vec<PortBinding>,
    },
}

impl Intension {
    pub fn canonicalize(&mut self) {
        match self {
            Intension::Primitive { .. } => {}
            Intension::Derive { premises, .. } => {
                premises.sort();
                premises.dedup();
            }
            Intension::Glue {
                parts: _,
                wiring,
                interface,
                ..
            } => {
                for (left, right) in wiring.iter_mut() {
                    if right < left {
                        std::mem::swap(left, right);
                    }
                }
                wiring.sort();
                wiring.dedup();
                interface.sort();
                interface.dedup();
            }
            Intension::Metaedge { ports, .. } => {
                ports.sort();
                ports.dedup();
            }
        }
    }

    pub fn key(&self) -> String {
        match self {
            Intension::Primitive { source } => exact_key("primitive", [source]),
            Intension::Derive {
                operation,
                premises,
            } => exact_key(
                "derive",
                std::iter::once(operation.as_str()).chain(premises.iter().map(|p| p.as_str())),
            ),
            Intension::Glue {
                operation,
                parts,
                wiring,
                interface,
            } => {
                let mut fields = vec![operation.clone()];
                fields.extend(parts.iter().map(ToString::to_string));
                fields.extend(wiring.iter().map(|(a, b)| format!("{a}={b}")));
                fields.extend(interface.iter().map(|p| format!("port:{p}")));
                exact_key("glue", &fields)
            }
            Intension::Metaedge { relation, ports } => {
                let mut fields = vec![relation.to_string()];
                fields.extend(ports.iter().map(|p| format!("{}:{}", p.role, p.target)));
                exact_key("metaedge", &fields)
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entity {
    pub id: EntityId,
    pub intension: Intension,
    pub bases: Vec<EvidenceId>,
}

impl Entity {
    pub fn new(mut intension: Intension, mut bases: Vec<EvidenceId>) -> Self {
        intension.canonicalize();
        bases.sort();
        bases.dedup();
        let intension_key = intension.key();
        // Evidence and context may change while the constructed occurrence
        // remains the same.  They therefore cannot participate in identity:
        // the immutable intension is the entity's identity boundary.
        let id = EntityId::derived("entity", [intension_key.as_str()]);
        Self {
            id,
            intension,
            bases,
        }
    }
}

/// One AND-node in the provenance graph. Each premise is an OR-node claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Evidence {
    pub id: EvidenceId,
    pub conclusion: ClaimId,
    pub operation: String,
    pub premises: Vec<ClaimId>,
    pub strength: Strength,
    pub context: Plane,
}

impl Evidence {
    pub fn new(
        conclusion: ClaimId,
        operation: impl Into<String>,
        mut premises: Vec<ClaimId>,
        strength: Strength,
        context: Plane,
    ) -> Self {
        let operation = operation.into();
        premises.sort();
        premises.dedup();
        let mut evidence = Self {
            id: EvidenceId::named("pending-evidence", "pending"),
            conclusion,
            operation,
            premises,
            strength,
            context,
        };
        evidence.reidentify();
        evidence
    }

    /// Recompute the content ID after an evaluator settles effective strength.
    pub fn reidentify(&mut self) {
        let plane = plane_to_string(&self.context);
        let strength = match self.strength {
            Strength::Strict => "strict",
            Strength::Defeasible => "defeasible",
        };
        self.id = EvidenceId::derived(
            "evidence",
            [
                self.conclusion.as_str(),
                self.operation.as_str(),
                strength,
                plane.as_str(),
            ]
            .into_iter()
            .chain(self.premises.iter().map(|p| p.as_str())),
        );
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Projection<T> {
    pub claim: ClaimId,
    pub entity: EntityId,
    pub context: Plane,
    pub extent: T,
    pub evidence: EvidenceId,
}

impl<T> Projection<T> {
    pub fn new(entity: &Entity, context: Plane, extent: T, evidence: &Evidence) -> Self {
        Self {
            claim: evidence.conclusion.clone(),
            entity: entity.id.clone(),
            context,
            extent,
            evidence: evidence.id.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Metaedge {
    pub entity: Entity,
    pub relation: EntityId,
    pub ports: Vec<PortBinding>,
    pub context: Plane,
    pub evidence: EvidenceId,
}

impl Metaedge {
    pub fn new(
        relation: EntityId,
        mut ports: Vec<PortBinding>,
        context: Plane,
        evidence: &Evidence,
    ) -> Self {
        ports.sort();
        ports.dedup();
        let entity = Entity::new(
            Intension::Metaedge {
                relation: relation.clone(),
                ports: ports.clone(),
            },
            vec![evidence.id.clone()],
        );
        Self {
            entity,
            relation,
            ports,
            context,
            evidence: evidence.id.clone(),
        }
    }
}
