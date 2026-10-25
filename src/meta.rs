//! Common proof-relevant carrier shared by evaluators and relation builders.
//!
//! A claim is an OR node: it may have several pieces of evidence. Evidence is
//! an AND node: all premise claims are required. An entity is the stable
//! occurrence built by one intension; a projection says what that occurrence
//! denotes in one context. None of these IDs is derived from an extent alone.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fmt::Write as _;

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
                interface: _,
                ..
            } => {
                for (left, right) in wiring.iter_mut() {
                    if right < left {
                        std::mem::swap(left, right);
                    }
                }
                wiring.sort();
                wiring.dedup();
                // The boundary is ordered and may repeat a port: (x, y),
                // (y, x), and (x, x) are different relation interfaces.
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

    fn entities(&self) -> Vec<&EntityId> {
        match self {
            Intension::Primitive { .. } | Intension::Derive { .. } => Vec::new(),
            Intension::Glue { parts, .. } => parts.iter().collect(),
            Intension::Metaedge { relation, ports } => std::iter::once(relation)
                .chain(ports.iter().map(|port| &port.target))
                .collect(),
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
    /// Context in which this derivation was evaluated.
    pub context: Plane,
    /// Plane on which the fact or operation itself was declared. This is
    /// distinct from `context`: a root rule may be evaluated in many more
    /// specific contexts while retaining its original specificity.
    pub source_context: Plane,
}

impl Evidence {
    pub fn new(
        conclusion: ClaimId,
        operation: impl Into<String>,
        premises: Vec<ClaimId>,
        strength: Strength,
        context: Plane,
    ) -> Self {
        Self::new_situated(
            conclusion,
            operation,
            premises,
            strength,
            context.clone(),
            context,
        )
    }

    pub fn new_situated(
        conclusion: ClaimId,
        operation: impl Into<String>,
        mut premises: Vec<ClaimId>,
        strength: Strength,
        context: Plane,
        source_context: Plane,
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
            source_context,
        };
        evidence.reidentify();
        evidence
    }

    /// Recompute the content ID after an evaluator settles effective strength.
    pub fn reidentify(&mut self) {
        let plane = plane_to_string(&self.context);
        let source_plane = plane_to_string(&self.source_context);
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
                source_plane.as_str(),
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvidenceState {
    Active,
    Retracted,
    Unsupported,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqualAt {
    pub left: EntityId,
    pub right: EntityId,
    pub context: Plane,
    pub evidence: EvidenceId,
}

/// Persistent semantic index over records emitted by the real executors.
/// Removal is deliberately absent: retraction changes the computed status,
/// while entities, projections, links, and their evidence remain in history.
#[derive(Clone, Debug, Default)]
pub struct Metagraph<T> {
    entities: BTreeMap<EntityId, Entity>,
    evidence: BTreeMap<EvidenceId, Evidence>,
    projections: Vec<Projection<T>>,
    metaedges: BTreeMap<EntityId, Metaedge>,
    equalities: Vec<EqualAt>,
    retractions: BTreeMap<EvidenceId, EvidenceId>,
}

impl<T: Clone + PartialEq> Metagraph<T> {
    pub fn new() -> Self {
        Self {
            entities: BTreeMap::new(),
            evidence: BTreeMap::new(),
            projections: Vec::new(),
            metaedges: BTreeMap::new(),
            equalities: Vec::new(),
            retractions: BTreeMap::new(),
        }
    }

    pub fn add_evidence(&mut self, evidence: Evidence) -> Result<(), String> {
        match self.evidence.get(&evidence.id) {
            Some(old) if old == &evidence => return Ok(()),
            Some(_) => return Err(format!("conflicting evidence `{}`", evidence.id)),
            None => {}
        }
        self.evidence.insert(evidence.id.clone(), evidence);
        Ok(())
    }

    pub fn add_entity(&mut self, mut entity: Entity) -> Result<(), String> {
        for dependency in entity.intension.entities() {
            if !self.entities.contains_key(dependency) {
                return Err(format!("unknown entity `{dependency}`"));
            }
        }
        for basis in &entity.bases {
            if !self.evidence.contains_key(basis) {
                return Err(format!("unknown entity basis `{basis}`"));
            }
        }
        if let Some(old) = self.entities.get_mut(&entity.id) {
            if old.intension != entity.intension {
                return Err(format!("conflicting entity `{}`", entity.id));
            }
            old.bases.append(&mut entity.bases);
            old.bases.sort();
            old.bases.dedup();
            return Ok(());
        }
        self.entities.insert(entity.id.clone(), entity);
        Ok(())
    }

    pub fn add_projection(&mut self, projection: Projection<T>) -> Result<(), String> {
        if !self.entities.contains_key(&projection.entity) {
            return Err(format!("unknown projected entity `{}`", projection.entity));
        }
        if !self.evidence.contains_key(&projection.evidence) {
            return Err(format!(
                "unknown projection evidence `{}`",
                projection.evidence
            ));
        }
        if let Some(old) = self
            .projections
            .iter()
            .find(|old| old.entity == projection.entity && old.context == projection.context)
        {
            if old.extent != projection.extent {
                return Err(format!(
                    "conflicting projection for `{}` in {}",
                    projection.entity,
                    plane_to_string(&projection.context)
                ));
            }
        }
        if !self.projections.contains(&projection) {
            self.projections.push(projection);
            self.projections.sort_by(|a, b| {
                (&a.context, &a.entity, &a.claim, &a.evidence).cmp(&(
                    &b.context,
                    &b.entity,
                    &b.claim,
                    &b.evidence,
                ))
            });
        }
        Ok(())
    }

    pub fn add_metaedge(&mut self, metaedge: Metaedge) -> Result<(), String> {
        if !self.evidence.contains_key(&metaedge.evidence) {
            return Err(format!("unknown metaedge evidence `{}`", metaedge.evidence));
        }
        self.add_entity(metaedge.entity.clone())?;
        match self.metaedges.get(&metaedge.entity.id) {
            Some(old) if old == &metaedge => Ok(()),
            Some(_) => Err(format!("conflicting metaedge `{}`", metaedge.entity.id)),
            None => {
                self.metaedges.insert(metaedge.entity.id.clone(), metaedge);
                Ok(())
            }
        }
    }

    pub fn add_equal_at(
        &mut self,
        left: EntityId,
        right: EntityId,
        context: Plane,
        evidence: EvidenceId,
    ) -> Result<(), String> {
        if !self.evidence.contains_key(&evidence) {
            return Err(format!("unknown equality evidence `{evidence}`"));
        }
        let left_extent = self.extent(&left, &context);
        let right_extent = self.extent(&right, &context);
        if left_extent.is_none() || right_extent.is_none() {
            return Err("equality needs both projections in its context".into());
        }
        if left_extent != right_extent {
            return Err("the two context projections are not equal".into());
        }
        let equality = EqualAt {
            left,
            right,
            context,
            evidence,
        };
        if !self.equalities.contains(&equality) {
            self.equalities.push(equality);
            self.equalities.sort_by(|a, b| {
                (&a.context, &a.left, &a.right, &a.evidence).cmp(&(
                    &b.context,
                    &b.left,
                    &b.right,
                    &b.evidence,
                ))
            });
        }
        Ok(())
    }

    pub fn retract(&mut self, target: EvidenceId, by: EvidenceId) -> Result<(), String> {
        if !self.evidence.contains_key(&target) {
            return Err(format!("unknown retraction target `{target}`"));
        }
        if !self.evidence.contains_key(&by) {
            return Err(format!("unknown retraction evidence `{by}`"));
        }
        self.retractions.insert(target, by);
        Ok(())
    }

    fn active_evidence_ids(&self) -> BTreeSet<EvidenceId> {
        let mut active = BTreeSet::new();
        loop {
            let mut changed = false;
            for evidence in self.evidence.values() {
                if active.contains(&evidence.id) || self.retractions.contains_key(&evidence.id) {
                    continue;
                }
                let supported = evidence.premises.iter().all(|premise| {
                    self.evidence.values().any(|candidate| {
                        candidate.conclusion == *premise
                            && active.contains(&candidate.id)
                            && visible_in(&candidate.context, &evidence.context)
                    })
                });
                if supported {
                    active.insert(evidence.id.clone());
                    changed = true;
                }
            }
            if !changed {
                return active;
            }
        }
    }

    pub fn evidence_state(&self, id: &EvidenceId) -> Option<EvidenceState> {
        if !self.evidence.contains_key(id) {
            return None;
        }
        if self.retractions.contains_key(id) {
            return Some(EvidenceState::Retracted);
        }
        Some(if self.active_evidence_ids().contains(id) {
            EvidenceState::Active
        } else {
            EvidenceState::Unsupported
        })
    }

    pub fn entity_active(&self, id: &EntityId) -> bool {
        let active = self.active_evidence_ids();
        self.entities
            .get(id)
            .is_some_and(|entity| entity.bases.iter().any(|basis| active.contains(basis)))
    }

    pub fn projection_active(&self, projection: &Projection<T>) -> bool {
        self.entity_active(&projection.entity)
            && self.active_evidence_ids().contains(&projection.evidence)
    }

    pub fn extent(&self, entity: &EntityId, context: &Plane) -> Option<&T> {
        self.projections
            .iter()
            .find(|p| &p.entity == entity && &p.context == context)
            .map(|p| &p.extent)
    }

    pub fn entities_with_extent(&self, context: &Plane, extent: &T) -> Vec<EntityId> {
        let mut entities: Vec<_> = self
            .projections
            .iter()
            .filter(|p| &p.context == context && &p.extent == extent)
            .map(|p| p.entity.clone())
            .collect();
        entities.sort();
        entities.dedup();
        entities
    }

    pub fn metaedges_using(&self, entity: &EntityId) -> Vec<&Metaedge> {
        self.metaedges
            .values()
            .filter(|edge| edge.ports.iter().any(|port| &port.target == entity))
            .collect()
    }

    pub fn metaedge_active(&self, edge: &Metaedge) -> bool {
        self.entity_active(&edge.entity.id)
            && self.entity_active(&edge.relation)
            && edge
                .ports
                .iter()
                .all(|port| self.entity_active(&port.target))
    }

    pub fn equalities(&self) -> &[EqualAt] {
        &self.equalities
    }

    pub fn equality_active(&self, equality: &EqualAt) -> bool {
        self.entity_active(&equality.left)
            && self.entity_active(&equality.right)
            && self.active_evidence_ids().contains(&equality.evidence)
    }

    pub fn entities(&self) -> impl Iterator<Item = &Entity> {
        self.entities.values()
    }

    pub fn evidence(&self) -> impl Iterator<Item = &Evidence> {
        self.evidence.values()
    }

    pub fn projections(&self) -> impl Iterator<Item = &Projection<T>> {
        self.projections.iter()
    }

    pub fn metaedges(&self) -> impl Iterator<Item = &Metaedge> {
        self.metaedges.values()
    }
}

impl<T: Clone + PartialEq + fmt::Debug> Metagraph<T> {
    /// Canonical semantic snapshot for regression tests and future replay.
    /// It is deliberately derived from records, never used as their identity.
    pub fn report(&self) -> String {
        let active = self.active_evidence_ids();
        let entity_active = |id: &EntityId| {
            self.entities
                .get(id)
                .is_some_and(|entity| entity.bases.iter().any(|basis| active.contains(basis)))
        };
        let mut out = String::new();
        for entity in self.entities.values() {
            writeln!(
                out,
                "entity {} {} {} bases={:?}",
                entity.id,
                if entity_active(&entity.id) {
                    "active"
                } else {
                    "inactive"
                },
                entity.intension.key(),
                entity.bases
            )
            .unwrap();
        }
        for evidence in self.evidence.values() {
            writeln!(
                out,
                "evidence {} {:?} claim={} at={} source={} premises={:?}",
                evidence.id,
                if self.retractions.contains_key(&evidence.id) {
                    EvidenceState::Retracted
                } else if active.contains(&evidence.id) {
                    EvidenceState::Active
                } else {
                    EvidenceState::Unsupported
                },
                evidence.conclusion,
                plane_to_string(&evidence.context),
                plane_to_string(&evidence.source_context),
                evidence.premises
            )
            .unwrap();
        }
        for projection in &self.projections {
            writeln!(
                out,
                "projection {} at={} {} evidence={} extent={:?}",
                projection.entity,
                plane_to_string(&projection.context),
                if entity_active(&projection.entity) && active.contains(&projection.evidence) {
                    "active"
                } else {
                    "inactive"
                },
                projection.evidence,
                projection.extent
            )
            .unwrap();
        }
        for equality in &self.equalities {
            writeln!(
                out,
                "equal {} {} at={} {} evidence={}",
                equality.left,
                equality.right,
                plane_to_string(&equality.context),
                if entity_active(&equality.left)
                    && entity_active(&equality.right)
                    && active.contains(&equality.evidence)
                {
                    "active"
                } else {
                    "inactive"
                },
                equality.evidence
            )
            .unwrap();
        }
        for edge in self.metaedges.values() {
            writeln!(
                out,
                "metaedge {} relation={} at={} {} ports={:?} evidence={}",
                edge.entity.id,
                edge.relation,
                plane_to_string(&edge.context),
                if entity_active(&edge.entity.id)
                    && entity_active(&edge.relation)
                    && edge.ports.iter().all(|port| entity_active(&port.target))
                {
                    "active"
                } else {
                    "inactive"
                },
                edge.ports,
                edge.evidence
            )
            .unwrap();
        }
        for (target, by) in &self.retractions {
            writeln!(out, "retract {target} by={by}").unwrap();
        }
        out
    }
}

/// The ordinary visibility order used by the current plane representation:
/// a record from a less specific plane is visible in a more specific one.
fn visible_in(source: &Plane, target: &Plane) -> bool {
    source
        .iter()
        .all(|(axis, value)| target.get(axis) == Some(value))
}
