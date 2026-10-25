//! Append-only serialization and verified replay of the shared metacore.
//!
//! The generic journal checks record hashes and dependency order. This module
//! gives its bodies a typed, versioned meaning for finite exact relations.

use std::collections::BTreeMap;

use crate::bank::{ExactRelation, Ext};
use crate::journal::Journal;
use crate::meta::{
    ClaimId, Entity, EntityId, Evidence, EvidenceId, Intension, Metaedge, Metagraph, PortBinding,
    Projection,
};
use crate::model::{Plane, Strength};

const KIND: &str = "metacore";
const STAGE: &str = "v1";

fn hex(text: &str) -> String {
    text.as_bytes()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn unhex(text: &str) -> Result<String, String> {
    if !text.len().is_multiple_of(2) {
        return Err("odd hex string".into());
    }
    let bytes = (0..text.len())
        .step_by(2)
        .map(|at| u8::from_str_radix(&text[at..at + 2], 16).map_err(|_| "bad hex".to_string()))
        .collect::<Result<Vec<_>, _>>()?;
    String::from_utf8(bytes).map_err(|_| "non-UTF-8 journal field".into())
}

fn list<'a>(items: impl IntoIterator<Item = &'a str>) -> String {
    items.into_iter().map(hex).collect::<Vec<_>>().join(",")
}

fn unlist(text: &str) -> Result<Vec<String>, String> {
    if text.is_empty() {
        return Ok(Vec::new());
    }
    text.split(',').map(unhex).collect()
}

fn plane(plane: &Plane) -> String {
    let text = plane
        .iter()
        .map(|(axis, value)| format!("{}={}", hex(axis), hex(value)))
        .collect::<Vec<_>>()
        .join(",");
    hex(&text)
}

fn unplane(encoded: &str) -> Result<Plane, String> {
    let text = unhex(encoded)?;
    if text.is_empty() {
        return Ok(Plane::new());
    }
    text.split(',')
        .map(|pair| {
            let (axis, value) = pair
                .split_once('=')
                .ok_or_else(|| "bad plane field".to_string())?;
            Ok((unhex(axis)?, unhex(value)?))
        })
        .collect()
}

fn ports(ports: &[PortBinding]) -> String {
    let text = ports
        .iter()
        .map(|port| format!("{}={}", hex(&port.role), hex(port.target.as_str())))
        .collect::<Vec<_>>()
        .join(",");
    hex(&text)
}

fn unports(encoded: &str) -> Result<Vec<PortBinding>, String> {
    let text = unhex(encoded)?;
    if text.is_empty() {
        return Ok(Vec::new());
    }
    text.split(',')
        .map(|binding| {
            let (role, target) = binding
                .split_once('=')
                .ok_or_else(|| "bad port binding".to_string())?;
            Ok(PortBinding::new(
                unhex(role)?,
                EntityId::from_stable_key(unhex(target)?),
            ))
        })
        .collect()
}

fn intension(intension: &Intension) -> String {
    let fields = match intension {
        Intension::Primitive { source } => vec!["p".into(), hex(source)],
        Intension::Derive {
            operation,
            premises,
        } => vec![
            "d".into(),
            hex(operation),
            list(premises.iter().map(|claim| claim.as_str())),
        ],
        Intension::Glue {
            operation,
            parts,
            wiring,
            interface,
        } => {
            let wiring = wiring
                .iter()
                .map(|(left, right)| format!("{}={}", hex(left), hex(right)))
                .collect::<Vec<_>>()
                .join(",");
            vec![
                "g".into(),
                hex(operation),
                list(parts.iter().map(|entity| entity.as_str())),
                hex(&wiring),
                list(interface.iter().map(String::as_str)),
            ]
        }
        Intension::Metaedge {
            source,
            relation,
            ports: bindings,
        } => vec![
            "m".into(),
            hex(source),
            hex(relation.as_str()),
            ports(bindings),
        ],
    };
    fields.join("|")
}

fn unintension(encoded: &str) -> Result<Intension, String> {
    let fields: Vec<&str> = encoded.split('|').collect();
    match fields.as_slice() {
        ["p", source] => Ok(Intension::Primitive {
            source: unhex(source)?,
        }),
        ["d", operation, premises] => Ok(Intension::Derive {
            operation: unhex(operation)?,
            premises: unlist(premises)?
                .into_iter()
                .map(ClaimId::from_stable_key)
                .collect(),
        }),
        ["g", operation, parts, wiring, interface] => {
            let wiring = unhex(wiring)?;
            let wiring = if wiring.is_empty() {
                Vec::new()
            } else {
                wiring
                    .split(',')
                    .map(|pair| {
                        let (left, right) = pair
                            .split_once('=')
                            .ok_or_else(|| "bad wiring".to_string())?;
                        Ok((unhex(left)?, unhex(right)?))
                    })
                    .collect::<Result<_, String>>()?
            };
            Ok(Intension::Glue {
                operation: unhex(operation)?,
                parts: unlist(parts)?
                    .into_iter()
                    .map(EntityId::from_stable_key)
                    .collect(),
                wiring,
                interface: unlist(interface)?,
            })
        }
        ["m", source, relation, bindings] => Ok(Intension::Metaedge {
            source: unhex(source)?,
            relation: EntityId::from_stable_key(unhex(relation)?),
            ports: unports(bindings)?,
        }),
        _ => Err("unknown intension record".into()),
    }
}

fn fields(body: &str, count: usize) -> Result<Vec<&str>, String> {
    let fields: Vec<_> = body.split('|').collect();
    if fields.len() != count {
        return Err(format!("expected {count} fields, got {}", fields.len()));
    }
    Ok(fields)
}

impl Metagraph<ExactRelation> {
    /// Append a deterministic, dependency-ordered snapshot as typed events.
    pub fn append_journal(&self, journal: &mut Journal) -> Result<(), String> {
        let mut evidence_records = BTreeMap::new();
        for evidence in self.evidence() {
            let strength = match evidence.strength {
                Strength::Strict => "s",
                Strength::Defeasible => "d",
            };
            let body = [
                hex(evidence.id.as_str()),
                hex(evidence.conclusion.as_str()),
                hex(&evidence.operation),
                strength.into(),
                plane(&evidence.context),
                plane(&evidence.source_context),
                list(evidence.premises.iter().map(|claim| claim.as_str())),
            ]
            .join("|");
            let record = journal.add(KIND, "evidence", STAGE, false, &[], &body);
            evidence_records.insert(evidence.id.clone(), record);
        }

        let mut entity_records = BTreeMap::new();
        let mut pending: Vec<_> = self.entities().collect();
        while !pending.is_empty() {
            let before = pending.len();
            let mut next = Vec::new();
            for entity in pending {
                if !entity
                    .intension
                    .dependencies()
                    .iter()
                    .all(|dependency| entity_records.contains_key(*dependency))
                {
                    next.push(entity);
                    continue;
                }
                let mut from = entity
                    .bases
                    .iter()
                    .map(|basis| {
                        evidence_records
                            .get(basis)
                            .copied()
                            .ok_or_else(|| format!("missing entity basis `{basis}`"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                from.extend(
                    entity
                        .intension
                        .dependencies()
                        .iter()
                        .map(|dependency| entity_records[*dependency]),
                );
                from.sort_unstable();
                from.dedup();
                let body = [
                    hex(entity.id.as_str()),
                    hex(&intension(&entity.intension)),
                    list(entity.bases.iter().map(|basis| basis.as_str())),
                ]
                .join("|");
                let record = journal.add(KIND, "entity", STAGE, false, &from, &body);
                entity_records.insert(entity.id.clone(), record);
            }
            if next.len() == before {
                return Err("entity dependency cycle while journaling".into());
            }
            pending = next;
        }

        let mut projection_records = BTreeMap::new();
        for projection in self.projections() {
            let storage = match projection.extent {
                ExactRelation::Dense(_) => "d",
                ExactRelation::Sparse { .. } => "s",
            };
            let pairs = projection
                .extent
                .pairs()
                .iter()
                .map(|(left, right)| format!("{left},{right}"))
                .collect::<Vec<_>>()
                .join(";");
            let body = [
                hex(projection.claim.as_str()),
                hex(projection.entity.as_str()),
                plane(&projection.context),
                hex(projection.evidence.as_str()),
                storage.into(),
                projection.extent.n().to_string(),
                hex(&pairs),
            ]
            .join("|");
            let from = [
                entity_records[&projection.entity],
                evidence_records[&projection.evidence],
            ];
            let record = journal.add(KIND, "projection", STAGE, false, &from, &body);
            projection_records.insert(
                (projection.entity.clone(), projection.context.clone()),
                record,
            );
        }

        for edge in self.metaedges() {
            let mut from = vec![
                entity_records[&edge.entity.id],
                entity_records[&edge.relation],
                evidence_records[&edge.evidence],
            ];
            from.extend(edge.ports.iter().map(|port| entity_records[&port.target]));
            from.sort_unstable();
            from.dedup();
            let body = [
                hex(edge.entity.id.as_str()),
                hex(edge.relation.as_str()),
                ports(&edge.ports),
                plane(&edge.context),
                hex(edge.evidence.as_str()),
            ]
            .join("|");
            journal.add(KIND, "metaedge", STAGE, false, &from, &body);
        }

        for equality in self.equalities() {
            let from = [
                projection_records[&(equality.left.clone(), equality.context.clone())],
                projection_records[&(equality.right.clone(), equality.context.clone())],
                evidence_records[&equality.evidence],
            ];
            let body = [
                hex(equality.left.as_str()),
                hex(equality.right.as_str()),
                plane(&equality.context),
                hex(equality.evidence.as_str()),
            ]
            .join("|");
            journal.add(KIND, "equality", STAGE, false, &from, &body);
        }

        for (target, by) in self.retractions() {
            let body = [hex(target.as_str()), hex(by.as_str())].join("|");
            let from = [evidence_records[target], evidence_records[by]];
            journal.add(KIND, "retract", STAGE, false, &from, &body);
        }
        Ok(())
    }

    /// Reconstruct a live metagraph from verified typed journal records.
    pub fn replay_journal(journal: &Journal) -> Result<Self, String> {
        let mut graph = Metagraph::new();
        for record in journal.records.iter().filter(|record| record.kind == KIND) {
            if record.stage != STAGE {
                return Err(format!("unsupported metacore stage `{}`", record.stage));
            }
            match record.step.as_str() {
                "evidence" => {
                    let f = fields(&record.body, 7)?;
                    let strength = match f[3] {
                        "s" => Strength::Strict,
                        "d" => Strength::Defeasible,
                        _ => return Err("bad evidence strength".into()),
                    };
                    let expected = EvidenceId::from_stable_key(unhex(f[0])?);
                    let evidence = Evidence::new_situated(
                        ClaimId::from_stable_key(unhex(f[1])?),
                        unhex(f[2])?,
                        unlist(f[6])?
                            .into_iter()
                            .map(ClaimId::from_stable_key)
                            .collect(),
                        strength,
                        unplane(f[4])?,
                        unplane(f[5])?,
                    );
                    if evidence.id != expected {
                        return Err("evidence stable id does not check".into());
                    }
                    graph.add_evidence(evidence)?;
                }
                "entity" => {
                    let f = fields(&record.body, 3)?;
                    let expected = EntityId::from_stable_key(unhex(f[0])?);
                    let entity = Entity::new(
                        unintension(&unhex(f[1])?)?,
                        unlist(f[2])?
                            .into_iter()
                            .map(EvidenceId::from_stable_key)
                            .collect(),
                    );
                    if entity.id != expected {
                        return Err("entity stable id does not check".into());
                    }
                    graph.add_entity(entity)?;
                }
                "projection" => {
                    let f = fields(&record.body, 7)?;
                    let n: usize = f[5].parse().map_err(|_| "bad relation size")?;
                    let pairs = unhex(f[6])?;
                    let pairs = if pairs.is_empty() {
                        Vec::new()
                    } else {
                        pairs
                            .split(';')
                            .map(|pair| {
                                let (left, right) = pair
                                    .split_once(',')
                                    .ok_or_else(|| "bad relation pair".to_string())?;
                                Ok((
                                    left.parse().map_err(|_| "bad pair value")?,
                                    right.parse().map_err(|_| "bad pair value")?,
                                ))
                            })
                            .collect::<Result<Vec<_>, String>>()?
                    };
                    let extent = match f[4] {
                        "d" => ExactRelation::dense(Ext::from_pairs(n, &pairs)),
                        "s" => ExactRelation::sparse(n, &pairs)?,
                        _ => return Err("bad exact-relation storage".into()),
                    };
                    graph.add_projection(Projection {
                        claim: ClaimId::from_stable_key(unhex(f[0])?),
                        entity: EntityId::from_stable_key(unhex(f[1])?),
                        context: unplane(f[2])?,
                        evidence: EvidenceId::from_stable_key(unhex(f[3])?),
                        extent,
                    })?;
                }
                "metaedge" => {
                    let f = fields(&record.body, 5)?;
                    let entity_id = EntityId::from_stable_key(unhex(f[0])?);
                    let entity = graph
                        .entity(&entity_id)
                        .cloned()
                        .ok_or_else(|| format!("unknown metaedge entity `{entity_id}`"))?;
                    graph.add_metaedge(Metaedge {
                        entity,
                        relation: EntityId::from_stable_key(unhex(f[1])?),
                        ports: unports(f[2])?,
                        context: unplane(f[3])?,
                        evidence: EvidenceId::from_stable_key(unhex(f[4])?),
                    })?;
                }
                "equality" => {
                    let f = fields(&record.body, 4)?;
                    graph.add_equal_at(
                        EntityId::from_stable_key(unhex(f[0])?),
                        EntityId::from_stable_key(unhex(f[1])?),
                        unplane(f[2])?,
                        EvidenceId::from_stable_key(unhex(f[3])?),
                    )?;
                }
                "retract" => {
                    let f = fields(&record.body, 2)?;
                    graph.retract(
                        EvidenceId::from_stable_key(unhex(f[0])?),
                        EvidenceId::from_stable_key(unhex(f[1])?),
                    )?;
                }
                other => return Err(format!("unknown metacore journal step `{other}`")),
            }
        }
        Ok(graph)
    }
}
