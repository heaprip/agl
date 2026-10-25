//! Stable relation occurrences, context-indexed projections and their evidence.
//!
//! This is the deliberately small semantic store exercised by
//! `tests/identity_extent.rs`. It reuses [`crate::model::Plane`],
//! [`crate::bank::Ext`] and [`crate::journal::Journal`]; it does not evaluate
//! rules or search for constructions.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Write as _};

use crate::bank::Ext;
use crate::journal::Journal;
use crate::model::{Plane, Strength, plane_to_string};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EntityId(String);

impl EntityId {
    pub fn new(id: impl Into<String>) -> Self {
        let id = id.into();
        assert!(!id.is_empty(), "an entity id cannot be empty");
        Self(id)
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for EntityId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EvidenceId(String);

impl EvidenceId {
    pub fn new(id: impl Into<String>) -> Self {
        let id = id.into();
        assert!(!id.is_empty(), "an evidence id cannot be empty");
        Self(id)
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for EvidenceId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// One endpoint of an open construction.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PortRef {
    pub entity: EntityId,
    pub role: String,
}

impl PortRef {
    pub fn new(entity: EntityId, role: impl Into<String>) -> Self {
        Self {
            entity,
            role: role.into(),
        }
    }
}

impl fmt::Display for PortRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}", self.entity, self.role)
    }
}

/// An immutable presentation of an entity. Projection is intentionally absent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Intension {
    Primitive {
        source: String,
    },
    Glue {
        parts: Vec<EntityId>,
        identifications: Vec<(PortRef, PortRef)>,
        interface: Vec<PortRef>,
    },
    /// Created only through [`Metagraph::add_metaedge`].
    Metaedge {
        relation: EntityId,
        ports: Vec<(String, EntityId)>,
    },
}

impl Intension {
    fn canonicalize(&mut self) {
        match self {
            Intension::Glue {
                parts,
                identifications,
                interface,
            } => {
                parts.sort();
                parts.dedup();
                for (a, b) in identifications.iter_mut() {
                    if *b < *a {
                        std::mem::swap(a, b);
                    }
                }
                identifications.sort();
                identifications.dedup();
                interface.sort();
                interface.dedup();
            }
            Intension::Metaedge { ports, .. } => ports.sort(),
            Intension::Primitive { .. } => {}
        }
    }

    fn references(&self) -> Vec<&EntityId> {
        match self {
            Intension::Primitive { .. } => Vec::new(),
            Intension::Glue {
                parts,
                identifications,
                interface,
            } => parts
                .iter()
                .chain(
                    identifications
                        .iter()
                        .flat_map(|(a, b)| [&a.entity, &b.entity]),
                )
                .chain(interface.iter().map(|p| &p.entity))
                .collect(),
            Intension::Metaedge { relation, ports } => std::iter::once(relation)
                .chain(ports.iter().map(|(_, entity)| entity))
                .collect(),
        }
    }
}

impl fmt::Display for Intension {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Intension::Primitive { source } => write!(f, "primitive({source})"),
            Intension::Glue {
                parts,
                identifications,
                interface,
            } => {
                let parts = parts.iter().map(ToString::to_string).collect::<Vec<_>>();
                let joins = identifications
                    .iter()
                    .map(|(a, b)| format!("{a}={b}"))
                    .collect::<Vec<_>>();
                let boundary = interface
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>();
                write!(
                    f,
                    "glue(parts=[{}], joins=[{}], interface=[{}])",
                    parts.join(","),
                    joins.join(","),
                    boundary.join(",")
                )
            }
            Intension::Metaedge { relation, ports } => {
                let ports = ports
                    .iter()
                    .map(|(role, entity)| format!("{role}:{entity}"))
                    .collect::<Vec<_>>();
                write!(f, "metaedge({relation}, [{}])", ports.join(","))
            }
        }
    }
}

/// Two physical representations of one exact finite binary relation.
#[derive(Clone, Debug)]
pub struct ExactRelation(ExactStorage);

#[derive(Clone, Debug)]
enum ExactStorage {
    Dense(Ext),
    Sparse {
        n: usize,
        pairs: BTreeSet<(usize, usize)>,
    },
}

impl ExactRelation {
    pub fn dense(n: usize, pairs: &[(usize, usize)]) -> Result<Self, String> {
        check_pairs(n, pairs)?;
        Ok(Self(ExactStorage::Dense(Ext::from_pairs(n, pairs))))
    }

    pub fn from_dense(extent: Ext) -> Self {
        Self(ExactStorage::Dense(extent))
    }

    pub fn sparse(n: usize, pairs: &[(usize, usize)]) -> Result<Self, String> {
        check_pairs(n, pairs)?;
        Ok(Self(ExactStorage::Sparse {
            n,
            pairs: pairs.iter().copied().collect(),
        }))
    }

    pub fn n(&self) -> usize {
        match &self.0 {
            ExactStorage::Dense(ext) => ext.n(),
            ExactStorage::Sparse { n, .. } => *n,
        }
    }

    pub fn contains(&self, a: usize, b: usize) -> bool {
        if a >= self.n() || b >= self.n() {
            return false;
        }
        match &self.0 {
            ExactStorage::Dense(ext) => ext.get(a, b),
            ExactStorage::Sparse { pairs, .. } => pairs.contains(&(a, b)),
        }
    }

    pub fn pairs(&self) -> Vec<(usize, usize)> {
        match &self.0 {
            ExactStorage::Dense(ext) => (0..ext.n())
                .flat_map(|a| (0..ext.n()).filter_map(move |b| ext.get(a, b).then_some((a, b))))
                .collect(),
            ExactStorage::Sparse { pairs, .. } => pairs.iter().copied().collect(),
        }
    }

    pub fn difference(&self, other: &Self) -> Vec<(usize, usize)> {
        self.pairs()
            .into_iter()
            .filter(|&(a, b)| !other.contains(a, b))
            .collect()
    }

    /// Reindex a source domain into a target domain; `None` forgets a point.
    pub fn restrict(&self, point_map: &[Option<usize>], target_n: usize) -> Result<Self, String> {
        if point_map.len() != self.n() {
            return Err(format!(
                "restriction maps {} points, relation has {}",
                point_map.len(),
                self.n()
            ));
        }
        if let Some(point) = point_map.iter().flatten().find(|&&p| p >= target_n) {
            return Err(format!("restriction target {point} is outside {target_n}"));
        }
        let pairs = self
            .pairs()
            .into_iter()
            .filter_map(|(a, b)| Some((point_map[a]?, point_map[b]?)))
            .collect::<Vec<_>>();
        ExactRelation::dense(target_n, &pairs)
    }
}

fn check_pairs(n: usize, pairs: &[(usize, usize)]) -> Result<(), String> {
    if let Some(&(a, b)) = pairs.iter().find(|&&(a, b)| a >= n || b >= n) {
        return Err(format!("pair ({a},{b}) is outside a domain of {n}"));
    }
    Ok(())
}

impl PartialEq for ExactRelation {
    fn eq(&self, other: &Self) -> bool {
        self.n() == other.n() && self.pairs() == other.pairs()
    }
}

impl Eq for ExactRelation {}

impl fmt::Display for ExactRelation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let pairs = self
            .pairs()
            .into_iter()
            .map(|(a, b)| format!("({a},{b})"))
            .collect::<Vec<_>>();
        write!(f, "n={} {{{}}}", self.n(), pairs.join(","))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operation {
    Input(String),
    Build,
    Observe,
    Compare,
    Link,
}

impl Operation {
    fn step(&self) -> &'static str {
        match self {
            Operation::Input(_) => "input",
            Operation::Build => "build",
            Operation::Observe => "observe",
            Operation::Compare => "compare",
            Operation::Link => "link",
        }
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operation::Input(source) => write!(f, "input({source})"),
            other => f.write_str(other.step()),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvidenceState {
    Active,
    Retracted,
    Unsupported,
}

impl fmt::Display for EvidenceState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvidenceState::Active => f.write_str("active"),
            EvidenceState::Retracted => f.write_str("retracted"),
            EvidenceState::Unsupported => f.write_str("unsupported"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Evidence {
    pub id: EvidenceId,
    pub premises: Vec<EvidenceId>,
    pub operation: Operation,
    pub strength: Strength,
    pub retracted_by: Option<EvidenceId>,
}

#[derive(Clone, Debug)]
pub struct Entity {
    pub id: EntityId,
    pub intension: Intension,
    pub bases: Vec<EvidenceId>,
}

#[derive(Clone, Debug)]
pub struct Projection {
    pub entity: EntityId,
    pub context: Plane,
    pub extent: ExactRelation,
    pub evidence: EvidenceId,
}

#[derive(Clone, Debug)]
pub struct EqualAt {
    pub left: EntityId,
    pub right: EntityId,
    pub context: Plane,
    pub evidence: EvidenceId,
}

#[derive(Clone, Debug)]
pub struct Metaedge {
    pub id: EntityId,
    pub relation: EntityId,
    pub ports: Vec<(String, EntityId)>,
    pub context: Plane,
    pub evidence: EvidenceId,
}

#[derive(Clone, Debug)]
pub struct Restriction {
    pub from: Plane,
    pub to: Plane,
    pub point_map: Vec<Option<usize>>,
    pub target_n: usize,
    pub evidence: EvidenceId,
}

#[derive(Default, Debug)]
pub struct Metagraph {
    entities: BTreeMap<EntityId, Entity>,
    evidence: BTreeMap<EvidenceId, Evidence>,
    projections: Vec<Projection>,
    equalities: Vec<EqualAt>,
    metaedges: BTreeMap<EntityId, Metaedge>,
    restrictions: Vec<Restriction>,
    journal: Journal,
    evidence_records: BTreeMap<EvidenceId, u64>,
    entity_records: BTreeMap<EntityId, u64>,
}

impl Metagraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn journal(&self) -> &Journal {
        &self.journal
    }

    pub fn add_evidence(
        &mut self,
        id: EvidenceId,
        mut premises: Vec<EvidenceId>,
        operation: Operation,
        strength: Strength,
    ) -> Result<(), String> {
        if self.evidence.contains_key(&id) {
            return Err(format!("duplicate evidence `{id}`"));
        }
        premises.sort();
        premises.dedup();
        for premise in &premises {
            if !self.evidence.contains_key(premise) {
                return Err(format!("unknown evidence premise `{premise}`"));
            }
        }
        let mut from = premises
            .iter()
            .map(|p| self.evidence_records[p])
            .collect::<Vec<_>>();
        from.sort_unstable();
        let stage = strength_name(strength);
        let record = self.journal.add(
            "evidence",
            operation.step(),
            stage,
            false,
            &from,
            &format!("id={id} operation={operation}"),
        );
        self.evidence_records.insert(id.clone(), record);
        self.evidence.insert(
            id.clone(),
            Evidence {
                id,
                premises,
                operation,
                strength,
                retracted_by: None,
            },
        );
        Ok(())
    }

    pub fn add_entity(
        &mut self,
        id: EntityId,
        intension: Intension,
        bases: Vec<EvidenceId>,
    ) -> Result<(), String> {
        if matches!(intension, Intension::Metaedge { .. }) {
            return Err("use add_metaedge for a metaedge entity".into());
        }
        self.insert_entity(id, intension, bases)
    }

    fn insert_entity(
        &mut self,
        id: EntityId,
        mut intension: Intension,
        mut bases: Vec<EvidenceId>,
    ) -> Result<(), String> {
        if self.entities.contains_key(&id) {
            return Err(format!("duplicate entity `{id}`"));
        }
        if bases.is_empty() {
            return Err(format!("entity `{id}` has no evidence"));
        }
        bases.sort();
        bases.dedup();
        for basis in &bases {
            if !self.evidence.contains_key(basis) {
                return Err(format!("unknown evidence `{basis}` for entity `{id}`"));
            }
        }
        intension.canonicalize();
        for reference in intension.references() {
            if !self.entities.contains_key(reference) {
                return Err(format!(
                    "intension of `{id}` references unknown `{reference}`"
                ));
            }
        }
        let mut from = bases
            .iter()
            .map(|basis| self.evidence_records[basis])
            .collect::<Vec<_>>();
        from.sort_unstable();
        let record = self.journal.add(
            "entity",
            "define",
            "identity",
            false,
            &from,
            &format!("id={id} intension={intension}"),
        );
        self.entity_records.insert(id.clone(), record);
        self.entities.insert(
            id.clone(),
            Entity {
                id,
                intension,
                bases,
            },
        );
        Ok(())
    }

    pub fn add_projection(&mut self, projection: Projection) -> Result<(), String> {
        let entity = self
            .entities
            .get(&projection.entity)
            .ok_or_else(|| format!("unknown projected entity `{}`", projection.entity))?;
        self.require_active_evidence(&projection.evidence)?;
        if !entity
            .bases
            .iter()
            .any(|basis| self.evidence_depends_on(&projection.evidence, basis))
        {
            return Err(format!(
                "projection evidence `{}` does not depend on entity `{}`",
                projection.evidence, projection.entity
            ));
        }
        if self.projections.iter().any(|p| {
            p.entity == projection.entity
                && p.context == projection.context
                && p.evidence == projection.evidence
        }) {
            return Err("duplicate projection evidence for entity and context".into());
        }
        let mut from = vec![
            self.evidence_records[&projection.evidence],
            self.entity_records[&projection.entity],
        ];
        from.sort_unstable();
        self.journal.add(
            "projection",
            "observe",
            "context",
            false,
            &from,
            &format!(
                "entity={} at={} extent={}",
                projection.entity,
                plane_to_string(&projection.context),
                projection.extent
            ),
        );
        self.projections.push(projection);
        Ok(())
    }

    pub fn add_equal_at(
        &mut self,
        mut left: EntityId,
        mut right: EntityId,
        context: Plane,
        evidence: EvidenceId,
    ) -> Result<(), String> {
        if right < left {
            std::mem::swap(&mut left, &mut right);
        }
        if left == right {
            return Err("EqualAt needs two distinct entities".into());
        }
        self.require_active_evidence(&evidence)?;
        let left_ps = self.active_projection_records(&left, &context);
        let right_ps = self.active_projection_records(&right, &context);
        let left_extent = left_ps
            .first()
            .ok_or_else(|| format!("no active projection of `{left}` in context"))?
            .extent
            .clone();
        if left_ps.iter().any(|p| p.extent != left_extent)
            || right_ps.is_empty()
            || right_ps.iter().any(|p| p.extent != left_extent)
        {
            return Err(format!(
                "projections of `{left}` and `{right}` are not equal"
            ));
        }
        for projections in [&left_ps, &right_ps] {
            if !projections
                .iter()
                .any(|p| self.evidence_depends_on(&evidence, &p.evidence))
            {
                return Err(format!(
                    "EqualAt evidence `{evidence}` does not depend on both projections"
                ));
            }
        }
        let record_from = self.evidence_records[&evidence];
        self.journal.add(
            "equality",
            "compare",
            "context",
            false,
            &[record_from],
            &format!("left={left} right={right} at={}", plane_to_string(&context)),
        );
        self.equalities.push(EqualAt {
            left,
            right,
            context,
            evidence,
        });
        Ok(())
    }

    pub fn add_metaedge(
        &mut self,
        id: EntityId,
        relation: EntityId,
        mut ports: Vec<(String, EntityId)>,
        context: Plane,
        evidence: EvidenceId,
    ) -> Result<(), String> {
        if ports.is_empty() {
            return Err("a metaedge must have an endpoint".into());
        }
        ports.sort();
        self.require_active_evidence(&evidence)?;
        for participant in std::iter::once(&relation).chain(ports.iter().map(|(_, e)| e)) {
            let entity = self
                .entities
                .get(participant)
                .ok_or_else(|| format!("unknown metaedge participant `{participant}`"))?;
            if !entity
                .bases
                .iter()
                .any(|basis| self.evidence_depends_on(&evidence, basis))
            {
                return Err(format!(
                    "metaedge evidence `{evidence}` does not depend on `{participant}`"
                ));
            }
        }
        self.insert_entity(
            id.clone(),
            Intension::Metaedge {
                relation: relation.clone(),
                ports: ports.clone(),
            },
            vec![evidence.clone()],
        )?;
        let mut from = vec![self.evidence_records[&evidence], self.entity_records[&id]];
        from.sort_unstable();
        self.journal.add(
            "metaedge",
            "link",
            "context",
            false,
            &from,
            &format!("id={id} at={}", plane_to_string(&context)),
        );
        self.metaedges.insert(
            id.clone(),
            Metaedge {
                id,
                relation,
                ports,
                context,
                evidence,
            },
        );
        Ok(())
    }

    pub fn add_restriction(&mut self, restriction: Restriction) -> Result<(), String> {
        self.require_active_evidence(&restriction.evidence)?;
        if let Some(point) = restriction
            .point_map
            .iter()
            .flatten()
            .find(|&&point| point >= restriction.target_n)
        {
            return Err(format!(
                "restriction target {point} is outside {}",
                restriction.target_n
            ));
        }
        let map = restriction
            .point_map
            .iter()
            .map(|p| p.map_or_else(|| "-".into(), |p| p.to_string()))
            .collect::<Vec<_>>();
        self.journal.add(
            "restriction",
            "reindex",
            "context",
            false,
            &[self.evidence_records[&restriction.evidence]],
            &format!(
                "from={} to={} map=[{}]",
                plane_to_string(&restriction.from),
                plane_to_string(&restriction.to),
                map.join(",")
            ),
        );
        self.restrictions.push(restriction);
        Ok(())
    }

    pub fn retract(&mut self, target: &EvidenceId, by: &EvidenceId) -> Result<(), String> {
        self.require_active_evidence(by)?;
        let evidence = self
            .evidence
            .get(target)
            .ok_or_else(|| format!("unknown retracted evidence `{target}`"))?;
        if evidence.retracted_by.is_some() {
            return Err(format!("evidence `{target}` is already retracted"));
        }
        if self.evidence_depends_on(by, target) {
            return Err(format!(
                "retraction `{by}` depends on its target `{target}`"
            ));
        }
        let mut from = vec![self.evidence_records[target], self.evidence_records[by]];
        from.sort_unstable();
        self.journal.add(
            "retraction",
            "retract",
            "direct",
            false,
            &from,
            &format!("target={target} by={by}"),
        );
        self.evidence.get_mut(target).unwrap().retracted_by = Some(by.clone());
        Ok(())
    }

    pub fn entity(&self, id: &EntityId) -> Option<&Entity> {
        self.entities.get(id)
    }

    pub fn evidence(&self, id: &EvidenceId) -> Option<&Evidence> {
        self.evidence.get(id)
    }

    pub fn evidence_ids(&self) -> impl Iterator<Item = &EvidenceId> {
        self.evidence.keys()
    }

    pub fn evidence_depends_on(&self, evidence: &EvidenceId, ancestor: &EvidenceId) -> bool {
        if evidence == ancestor {
            return true;
        }
        let mut seen = BTreeSet::new();
        let mut pending = vec![evidence];
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            let Some(record) = self.evidence.get(id) else {
                continue;
            };
            if record.premises.iter().any(|p| p == ancestor) {
                return true;
            }
            pending.extend(record.premises.iter());
        }
        false
    }

    pub fn evidence_state(&self, id: &EvidenceId) -> Option<EvidenceState> {
        fn state(
            graph: &Metagraph,
            id: &EvidenceId,
            memo: &mut BTreeMap<EvidenceId, EvidenceState>,
        ) -> Option<EvidenceState> {
            if let Some(&state) = memo.get(id) {
                return Some(state);
            }
            let evidence = graph.evidence.get(id)?;
            let result = if evidence.retracted_by.is_some() {
                EvidenceState::Retracted
            } else if evidence
                .premises
                .iter()
                .any(|premise| state(graph, premise, memo) != Some(EvidenceState::Active))
            {
                EvidenceState::Unsupported
            } else {
                EvidenceState::Active
            };
            memo.insert(id.clone(), result);
            Some(result)
        }
        state(self, id, &mut BTreeMap::new())
    }

    pub fn entity_active(&self, id: &EntityId) -> bool {
        self.entities.get(id).is_some_and(|entity| {
            entity
                .bases
                .iter()
                .any(|basis| self.evidence_state(basis) == Some(EvidenceState::Active))
        })
    }

    pub fn projections(&self) -> &[Projection] {
        &self.projections
    }

    pub fn equalities(&self) -> &[EqualAt] {
        &self.equalities
    }

    pub fn metaedges(&self) -> impl Iterator<Item = &Metaedge> {
        self.metaedges.values()
    }

    pub fn active_projections(&self) -> Vec<&Projection> {
        self.projections
            .iter()
            .filter(|p| {
                self.entity_active(&p.entity)
                    && self.evidence_state(&p.evidence) == Some(EvidenceState::Active)
            })
            .collect()
    }

    pub fn active_equalities(&self) -> Vec<&EqualAt> {
        self.equalities
            .iter()
            .filter(|equal| {
                self.entity_active(&equal.left)
                    && self.entity_active(&equal.right)
                    && self.evidence_state(&equal.evidence) == Some(EvidenceState::Active)
            })
            .collect()
    }

    pub fn active_metaedges(&self) -> Vec<&Metaedge> {
        self.metaedges
            .values()
            .filter(|edge| self.entity_active(&edge.id))
            .collect()
    }

    pub fn extent(&self, entity: &EntityId, context: &Plane) -> Result<&ExactRelation, String> {
        let projections = self.active_projection_records(entity, context);
        let first = projections
            .first()
            .ok_or_else(|| format!("no active projection of `{entity}` in context"))?;
        if projections.iter().any(|p| p.extent != first.extent) {
            return Err(format!("conflicting projections of `{entity}` in context"));
        }
        Ok(&first.extent)
    }

    pub fn entities_with_extent(&self, context: &Plane, extent: &ExactRelation) -> Vec<EntityId> {
        self.active_projections()
            .into_iter()
            .filter(|p| p.context == *context && p.extent == *extent)
            .map(|p| p.entity.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    pub fn metaedges_using(&self, entity: &EntityId) -> Vec<&Metaedge> {
        self.active_metaedges()
            .into_iter()
            .filter(|edge| edge.ports.iter().any(|(_, endpoint)| endpoint == entity))
            .collect()
    }

    pub fn restricted_projection(
        &self,
        entity: &EntityId,
        from: &Plane,
        to: &Plane,
    ) -> Result<ExactRelation, String> {
        let restrictions = self
            .restrictions
            .iter()
            .filter(|r| {
                r.from == *from
                    && r.to == *to
                    && self.evidence_state(&r.evidence) == Some(EvidenceState::Active)
            })
            .collect::<Vec<_>>();
        let [restriction] = restrictions.as_slice() else {
            return Err(format!(
                "expected one active restriction {} -> {}, found {}",
                plane_to_string(from),
                plane_to_string(to),
                restrictions.len()
            ));
        };
        self.extent(entity, from)?
            .restrict(&restriction.point_map, restriction.target_n)
    }

    /// Canonical semantic state. Journal order is deliberately not exposed here.
    pub fn report(&self) -> String {
        let mut out = String::new();
        for evidence in self.evidence.values() {
            let premises = evidence
                .premises
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>();
            writeln!(
                out,
                "evidence {} {} {} {} <- [{}]",
                evidence.id,
                self.evidence_state(&evidence.id).unwrap(),
                strength_name(evidence.strength),
                evidence.operation,
                premises.join(",")
            )
            .unwrap();
        }
        for entity in self.entities.values() {
            let bases = entity
                .bases
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>();
            writeln!(
                out,
                "entity {} {} {} <- [{}]",
                entity.id,
                if self.entity_active(&entity.id) {
                    "active"
                } else {
                    "inactive"
                },
                entity.intension,
                bases.join(",")
            )
            .unwrap();
        }
        let mut projections = self.projections.iter().collect::<Vec<_>>();
        projections.sort_by_key(|p| {
            (
                p.entity.clone(),
                plane_to_string(&p.context),
                p.evidence.clone(),
            )
        });
        for p in projections {
            writeln!(
                out,
                "projection {} {} at={} {} by={}",
                p.entity,
                if self.evidence_state(&p.evidence) == Some(EvidenceState::Active)
                    && self.entity_active(&p.entity)
                {
                    "active"
                } else {
                    "inactive"
                },
                plane_to_string(&p.context),
                p.extent,
                p.evidence
            )
            .unwrap();
        }
        let mut equalities = self.equalities.iter().collect::<Vec<_>>();
        equalities.sort_by_key(|e| (e.left.clone(), e.right.clone(), plane_to_string(&e.context)));
        for equal in equalities {
            writeln!(
                out,
                "equal-at {} {} {} at={} by={}",
                equal.left,
                equal.right,
                if self.evidence_state(&equal.evidence) == Some(EvidenceState::Active) {
                    "active"
                } else {
                    "inactive"
                },
                plane_to_string(&equal.context),
                equal.evidence
            )
            .unwrap();
        }
        for edge in self.metaedges.values() {
            let ports = edge
                .ports
                .iter()
                .map(|(role, entity)| format!("{role}:{entity}"))
                .collect::<Vec<_>>();
            writeln!(
                out,
                "metaedge {} {} relation={} ports=[{}] at={} by={}",
                edge.id,
                if self.entity_active(&edge.id) {
                    "active"
                } else {
                    "inactive"
                },
                edge.relation,
                ports.join(","),
                plane_to_string(&edge.context),
                edge.evidence
            )
            .unwrap();
        }
        let mut restrictions = self.restrictions.iter().collect::<Vec<_>>();
        restrictions.sort_by_key(|r| {
            (
                plane_to_string(&r.from),
                plane_to_string(&r.to),
                r.evidence.clone(),
            )
        });
        for restriction in restrictions {
            let map = restriction
                .point_map
                .iter()
                .map(|p| p.map_or_else(|| "-".into(), |p| p.to_string()))
                .collect::<Vec<_>>();
            writeln!(
                out,
                "restriction {} from={} to={} map=[{}] by={}",
                if self.evidence_state(&restriction.evidence) == Some(EvidenceState::Active) {
                    "active"
                } else {
                    "inactive"
                },
                plane_to_string(&restriction.from),
                plane_to_string(&restriction.to),
                map.join(","),
                restriction.evidence
            )
            .unwrap();
        }
        out
    }

    fn require_active_evidence(&self, id: &EvidenceId) -> Result<(), String> {
        match self.evidence_state(id) {
            Some(EvidenceState::Active) => Ok(()),
            Some(state) => Err(format!("evidence `{id}` is {state}")),
            None => Err(format!("unknown evidence `{id}`")),
        }
    }

    fn active_projection_records<'a>(
        &'a self,
        entity: &EntityId,
        context: &Plane,
    ) -> Vec<&'a Projection> {
        self.active_projections()
            .into_iter()
            .filter(|p| p.entity == *entity && p.context == *context)
            .collect()
    }
}

fn strength_name(strength: Strength) -> &'static str {
    match strength {
        Strength::Strict => "strict",
        Strength::Defeasible => "defeasible",
    }
}
