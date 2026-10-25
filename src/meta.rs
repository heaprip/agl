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
use crate::plane::Axes;

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

            /// Restore an exact stable key from a verified journal record.
            /// Normal construction should use `named` or `derived`.
            pub fn from_stable_key(key: impl Into<String>) -> Self {
                Self(key.into())
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

/// One occurrence in a structural composition. A hole is not a command to
/// another solver: it is an unfilled relation position in the same intension.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Part {
    Entity(EntityId),
    Hole(String),
}

impl Part {
    fn key(&self) -> String {
        match self {
            Part::Entity(entity) => entity.to_string(),
            Part::Hole(hole) => format!("?{hole}"),
        }
    }
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
        parts: Vec<Part>,
        wiring: Vec<(String, String)>,
        interface: Vec<String>,
    },
    /// A relation occurrence whose endpoints are themselves entities.
    Metaedge {
        source: String,
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
                fields.extend(parts.iter().map(Part::key));
                fields.extend(wiring.iter().map(|(a, b)| format!("{a}={b}")));
                fields.extend(interface.iter().map(|p| format!("port:{p}")));
                exact_key("glue", &fields)
            }
            Intension::Metaedge {
                source,
                relation,
                ports,
            } => {
                let mut fields = vec![source.clone(), relation.to_string()];
                fields.extend(ports.iter().map(|p| format!("{}:{}", p.role, p.target)));
                exact_key("metaedge", &fields)
            }
        }
    }

    pub fn dependencies(&self) -> Vec<&EntityId> {
        match self {
            Intension::Primitive { .. } | Intension::Derive { .. } => Vec::new(),
            Intension::Glue { parts, .. } => parts
                .iter()
                .filter_map(|part| match part {
                    Part::Entity(entity) => Some(entity),
                    Part::Hole(_) => None,
                })
                .collect(),
            Intension::Metaedge {
                relation, ports, ..
            } => std::iter::once(relation)
                .chain(ports.iter().map(|port| &port.target))
                .collect(),
        }
    }

    /// Names of the still-unfilled positions of this construction.
    pub fn holes(&self) -> BTreeSet<&str> {
        match self {
            Intension::Glue { parts, .. } => parts
                .iter()
                .filter_map(|part| match part {
                    Part::Hole(hole) => Some(hole.as_str()),
                    Part::Entity(_) => None,
                })
                .collect(),
            _ => BTreeSet::new(),
        }
    }

    /// Fill every occurrence of one named hole. The result is still the same
    /// structural intension; when its last hole is filled it is byte-for-byte
    /// equal to a directly constructed closed `Glue`.
    pub fn bind(&self, hole: &str, entity: EntityId) -> Result<Self, String> {
        let Intension::Glue {
            operation,
            parts,
            wiring,
            interface,
        } = self
        else {
            return Err("only a glue intension has open relation positions".into());
        };
        if !parts
            .iter()
            .any(|part| matches!(part, Part::Hole(name) if name == hole))
        {
            return Err(format!("unknown or already filled hole `{hole}`"));
        }
        Ok(Intension::Glue {
            operation: operation.clone(),
            parts: parts
                .iter()
                .map(|part| match part {
                    Part::Hole(name) if name == hole => Part::Entity(entity.clone()),
                    other => other.clone(),
                })
                .collect(),
            wiring: wiring.clone(),
            interface: interface.clone(),
        })
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
                source: evidence.operation.clone(),
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
        for dependency in entity.intension.dependencies() {
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

    fn entity_claim(&self, id: &EntityId) -> Result<ClaimId, String> {
        let entity = self
            .entities
            .get(id)
            .ok_or_else(|| format!("unknown entity `{id}`"))?;
        let mut claims = entity
            .bases
            .iter()
            .map(|basis| {
                self.evidence
                    .get(basis)
                    .map(|evidence| evidence.conclusion.clone())
                    .ok_or_else(|| format!("unknown entity basis `{basis}`"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        claims.sort();
        claims.dedup();
        match claims.as_slice() {
            [claim] => Ok(claim.clone()),
            [] => Err(format!("entity `{id}` has no construction evidence")),
            _ => Err(format!(
                "entity `{id}` bases do not support one construction claim"
            )),
        }
    }

    /// Active structural compositions which still contain unfilled relation
    /// positions. This is a derived view of ordinary entities, not a queue of
    /// special questions owned by another executor.
    pub fn open_frontier(&self) -> Vec<(EntityId, Vec<String>)> {
        let active = self.active_evidence_ids();
        self.entities
            .values()
            .filter(|entity| entity.bases.iter().any(|basis| active.contains(basis)))
            .filter_map(|entity| {
                let holes = entity
                    .intension
                    .holes()
                    .into_iter()
                    .map(str::to_string)
                    .collect::<Vec<_>>();
                (!holes.is_empty()).then(|| (entity.id.clone(), holes))
            })
            .collect()
    }

    /// Fill a relation position with another active entity. The operation
    /// produces ordinary evidence and an ordinary entity, so retraction and
    /// alternative provenance use the same AND/OR graph as every other step.
    pub fn bind_open(
        &mut self,
        open: &EntityId,
        hole: &str,
        part: &EntityId,
        context: Plane,
    ) -> Result<EntityId, String> {
        let active = self.active_evidence_ids();
        if !self
            .entities
            .get(open)
            .is_some_and(|entity| entity.bases.iter().any(|basis| active.contains(basis)))
        {
            return Err(format!("open entity `{open}` is not active"));
        }
        if !self
            .entities
            .get(part)
            .is_some_and(|entity| entity.bases.iter().any(|basis| active.contains(basis)))
        {
            return Err(format!("binding entity `{part}` is not active"));
        }
        self.bind_open_active(open, hole, part, context)
    }

    /// Bind one explicitly selected active entity at every compatible meet of
    /// the active construction evidence contexts for the two entities.
    pub fn bind_open_at_meets(
        &mut self,
        axes: &Axes,
        open: &EntityId,
        hole: &str,
        part: &EntityId,
    ) -> Result<Vec<(Plane, EntityId)>, String> {
        let open_entity = self
            .entities
            .get(open)
            .ok_or_else(|| format!("unknown open entity `{open}`"))?
            .clone();
        let part_entity = self
            .entities
            .get(part)
            .ok_or_else(|| format!("unknown binding entity `{part}`"))?
            .clone();
        let intension = open_entity.intension.bind(hole, part.clone())?;
        let active = self.active_evidence_ids_with_axes(axes);
        let contexts = |entity: &Entity| -> Vec<Plane> {
            entity
                .bases
                .iter()
                .filter(|basis| active.contains(*basis))
                .filter_map(|basis| self.evidence.get(basis))
                .map(|evidence| evidence.context.clone())
                .collect()
        };
        let open_bases = contexts(&open_entity);
        let part_bases = contexts(&part_entity);
        if open_bases.is_empty() {
            return Err(format!("open entity `{open}` is not active"));
        }
        if part_bases.is_empty() {
            return Err(format!("binding entity `{part}` is not active"));
        }
        let open_claim = self.entity_claim(open)?;
        let part_claim = self.entity_claim(part)?;
        let mut pairs = BTreeSet::new();
        for open_context in &open_bases {
            for part_context in &part_bases {
                let Some(context) = axes.plane_meet(open_context, part_context) else {
                    continue;
                };
                let provisional = Entity::new(intension.clone(), Vec::new());
                let evidence = Evidence::new_situated(
                    ClaimId::derived("entity", [provisional.id.as_str()]),
                    format!("bind-open:{hole}"),
                    vec![open_claim.clone(), part_claim.clone()],
                    Strength::Strict,
                    context.clone(),
                    Plane::new(),
                );
                self.add_evidence(evidence.clone())?;
                let entity = Entity::new(intension.clone(), vec![evidence.id]);
                let id = entity.id.clone();
                self.add_entity(entity)?;
                pairs.insert((context, id));
            }
        }
        Ok(pairs.into_iter().collect())
    }

    fn bind_open_active(
        &mut self,
        open: &EntityId,
        hole: &str,
        part: &EntityId,
        context: Plane,
    ) -> Result<EntityId, String> {
        let open_entity = self.entities[open].clone();
        let intension = open_entity.intension.bind(hole, part.clone())?;
        let provisional = Entity::new(intension.clone(), Vec::new());
        let evidence = Evidence::new_situated(
            ClaimId::derived("entity", [provisional.id.as_str()]),
            format!("bind-open:{hole}"),
            vec![self.entity_claim(open)?, self.entity_claim(part)?],
            Strength::Strict,
            context,
            Plane::new(),
        );
        self.add_evidence(evidence.clone())?;
        let entity = Entity::new(intension, vec![evidence.id]);
        let id = entity.id.clone();
        self.add_entity(entity)?;
        Ok(id)
    }

    /// Expand every active open composition with every active closed
    /// occurrence, breadth-first for at most `rounds` and `max_new` entities.
    /// The boolean result says that the size budget stopped expansion. This
    /// is deliberately domain-blind: later port types may prune candidates,
    /// but no anomaly kind dispatches to a different algorithm.
    pub fn expand_open_frontier(
        &mut self,
        context: Plane,
        rounds: usize,
        max_new: usize,
    ) -> Result<(Vec<EntityId>, bool), String> {
        let before: BTreeSet<_> = self.entities.keys().cloned().collect();
        let mut truncated = false;
        'rounds: for _ in 0..rounds {
            let active = self.active_evidence_ids();
            let frontier = self
                .entities
                .values()
                .filter(|entity| entity.bases.iter().any(|basis| active.contains(basis)))
                .filter_map(|entity| {
                    let holes = entity
                        .intension
                        .holes()
                        .into_iter()
                        .map(str::to_string)
                        .collect::<Vec<_>>();
                    (!holes.is_empty()).then(|| (entity.id.clone(), holes))
                })
                .collect::<Vec<_>>();
            let candidates = self
                .entities
                .values()
                .filter(|entity| {
                    entity.intension.holes().is_empty()
                        && entity.bases.iter().any(|basis| active.contains(basis))
                })
                .map(|entity| entity.id.clone())
                .collect::<Vec<_>>();
            let count = self.entities.len();
            for (open, holes) in frontier {
                for hole in holes {
                    for candidate in &candidates {
                        if self.entities.len().saturating_sub(before.len()) >= max_new {
                            truncated = true;
                            break 'rounds;
                        }
                        self.bind_open_active(&open, &hole, candidate, context.clone())?;
                    }
                }
            }
            if self.entities.len() == count {
                break;
            }
        }
        Ok((
            self.entities
                .keys()
                .filter(|entity| !before.contains(*entity))
                .cloned()
                .collect(),
            truncated,
        ))
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
            && old.extent != projection.extent
        {
            return Err(format!(
                "conflicting projection for `{}` in {}",
                projection.entity,
                plane_to_string(&projection.context)
            ));
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
        self.active_evidence_ids_by(visible_in)
    }

    fn active_evidence_ids_with_axes(&self, axes: &Axes) -> BTreeSet<EvidenceId> {
        self.active_evidence_ids_by(|source, target| axes.plane_within(target, source))
    }

    fn active_evidence_ids_by(
        &self,
        visible: impl Fn(&Plane, &Plane) -> bool,
    ) -> BTreeSet<EvidenceId> {
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
                            && visible(&candidate.context, &evidence.context)
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

    /// State of one evidence record under the declared context hierarchy and
    /// overlaps. The legacy context-free query remains available for callers
    /// which do not own an `Axes` registry.
    pub fn evidence_state_with_axes(&self, axes: &Axes, id: &EvidenceId) -> Option<EvidenceState> {
        if !self.evidence.contains_key(id) {
            return None;
        }
        if self.retractions.contains_key(id) {
            return Some(EvidenceState::Retracted);
        }
        Some(if self.active_evidence_ids_with_axes(axes).contains(id) {
            EvidenceState::Active
        } else {
            EvidenceState::Unsupported
        })
    }

    /// Whether an entity has an active construction basis when context
    /// inheritance and declared intersections are interpreted by `axes`.
    pub fn entity_active_with_axes(&self, axes: &Axes, id: &EntityId) -> bool {
        let active = self.active_evidence_ids_with_axes(axes);
        self.entities
            .get(id)
            .is_some_and(|entity| entity.bases.iter().any(|basis| active.contains(basis)))
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

    pub fn entity(&self, id: &EntityId) -> Option<&Entity> {
        self.entities.get(id)
    }

    pub fn retractions(&self) -> impl Iterator<Item = (&EvidenceId, &EvidenceId)> {
        self.retractions.iter()
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
