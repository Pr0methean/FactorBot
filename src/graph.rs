use crate::Factor::Complex;
use crate::NumberSpecifier::{Expression, Id};
use crate::ReportFactorResult::{Accepted, AlreadyFullyFactored, DoesNotDivide, OtherError};
use crate::algebraic::ComplexFactor::Multiply;
use crate::algebraic::Factor::Numeric;
use crate::algebraic::div_exact;
use crate::algebraic::{ComplexFactor, simplify_divide};
use crate::algebraic::{
    Factor, NumericFactor, estimate_log10, evaluate_as_numeric, find_unique_factors,
};
use crate::graph::Divisibility::{Direct, NotFactor, Transitive};
use crate::graph::FactorsKnownToFactorDb::{NotUpToDate, UpToDate};
use crate::net::NumberStatus::{FullyFactored, Invalid, PartlyFactoredComposite, Prime, UnfactoredComposite};
use crate::net::{
    FactorDbClient, FactorDbClientReadIdsAndExprs, NumberStatus, NumberStatusExt,
    ProcessedStatusApiResponse,
};
use crate::{FAILED_U_SUBMISSIONS_OUT, NumberLength, NumberSpecifier, SUBMIT_FACTOR_MAX_ATTEMPTS};
use alloc::borrow::Cow::Borrowed;
use alloc::vec::IntoIter;
use async_backtrace::framed;
use itertools::Itertools;
use log::{debug, error, info, warn};
use petgraph::Direction::{Incoming, Outgoing};
use petgraph::algo::spfa;
use petgraph::prelude::EdgeRef;
use petgraph::stable_graph::{NodeIndex, StableGraph};
use petgraph::visit::IntoEdgeReferences;
use petgraph::{Directed, Direction};
use rand::rng;
use rand::seq::SliceRandom;
use replace_with::replace_with_or_abort;
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::io::Write;
use std::mem::replace;
use std::sync::OnceLock;

pub type EntryId = u128;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Divisibility {
    NotFactor,
    Transitive,
    Direct,
}

pub type VertexId = NodeIndex; // Optional alias for compatibility

// Update DivisibilityGraph type
pub type DivisibilityGraph = StableGraph<Factor, Divisibility, Directed>;

pub struct FactorData {
    pub divisibility_graph: DivisibilityGraph,
    pub deleted_synonyms: BTreeMap<VertexId, VertexId>,
    pub number_facts_map: BTreeMap<VertexId, NumberFacts>,
    pub vertex_id_by_expr: BTreeMap<Factor, VertexId>,
    pub vertex_id_by_entry_id: BTreeMap<EntryId, VertexId>,
}

const DEFAULT_NODE_CAPACITY: usize = 256;

impl Default for FactorData {
    fn default() -> Self {
        FactorData {
            divisibility_graph: StableGraph::with_capacity(
                DEFAULT_NODE_CAPACITY,
                DEFAULT_NODE_CAPACITY * (DEFAULT_NODE_CAPACITY - 1),
            ),
            deleted_synonyms: BTreeMap::new(),
            number_facts_map: BTreeMap::new(),
            vertex_id_by_entry_id: BTreeMap::new(),
            vertex_id_by_expr: BTreeMap::new(),
        }
    }
}

#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq)]
enum WorkItem {
    Propagate {
        factor: VertexId,
        dest: VertexId,
        transitive: bool,
    },
    RuleOut {
        nonfactor: VertexId,
        dest: VertexId,
    },
}

impl FactorData {
    pub fn resolve_vid(&mut self, vertex_id: VertexId) -> VertexId {
        Self::resolve_vid_internal(&mut self.deleted_synonyms, vertex_id)
    }

    pub fn resolve_vid_internal(
        deleted_synonyms: &mut BTreeMap<VertexId, VertexId>,
        mut vertex_id: VertexId,
    ) -> VertexId {
        let mut synonyms_to_forward = Vec::new();
        while let Some(synonym) = deleted_synonyms.get(&vertex_id) {
            synonyms_to_forward.push(*synonym);
            vertex_id = *synonym;
        }
        if let Some(last) = synonyms_to_forward.last() {
            vertex_id = *last;
            // Optimization: path compression
            for synonym in synonyms_to_forward.into_iter().rev().skip(1) {
                deleted_synonyms.insert(synonym, vertex_id);
            }
        }
        vertex_id
    }

    pub fn vid_for_entry_id(&mut self, entry_id: EntryId) -> Option<VertexId> {
        let raw_vid = self.vertex_id_by_entry_id.get_mut(&entry_id)?;
        let vid = Self::resolve_vid_internal(&mut self.deleted_synonyms, *raw_vid);
        *raw_vid = vid;
        Some(vid)
    }

    pub fn vid_for_expr(&mut self, expr: &Factor) -> Option<VertexId> {
        let raw_vid = self.vertex_id_by_expr.get_mut(expr)?;
        let vid = Self::resolve_vid_internal(&mut self.deleted_synonyms, *raw_vid);
        *raw_vid = vid;
        Some(vid)
    }

    pub fn get_factor(&mut self, vertex_id: VertexId) -> Factor {
        let real_id = self.resolve_vid(vertex_id);
        self.divisibility_graph
            .node_weight(real_id)
            .unwrap()
            .clone()
    }

    pub fn facts(&mut self, vertex_id: VertexId) -> Option<&NumberFacts> {
        let real_id = self.resolve_vid(vertex_id);
        self.number_facts_map.get(&real_id)
    }

    pub fn facts_mut(&mut self, vertex_id: VertexId) -> &mut NumberFacts {
        let real_id = self.resolve_vid(vertex_id);
        self.number_facts_map.get_mut(&real_id).unwrap()
    }

    pub fn get_edge(&mut self, source: VertexId, dest: VertexId) -> Option<Divisibility> {
        let source = self.resolve_vid(source);
        let dest = self.resolve_vid(dest);
        let edge = self
            .divisibility_graph
            .edges_connecting(source, dest)
            .next()?;
        Some(*edge.weight())
    }

    pub fn rule_out_divisibility(&mut self, nonfactor: VertexId, dest: VertexId) {
        let mut worklist = BTreeSet::new();
        worklist.insert(WorkItem::RuleOut { nonfactor, dest });
        self.process_divisibility_worklist(worklist);
    }

    pub fn propagate_divisibility(&mut self, factor: VertexId, dest: VertexId, transitive: bool) {
        let mut worklist = BTreeSet::new();
        worklist.insert(WorkItem::Propagate {
            factor,
            dest,
            transitive,
        });
        self.process_divisibility_worklist(worklist);
    }

    fn process_divisibility_worklist(&mut self, mut worklist: BTreeSet<WorkItem>) {
        let mut already_processed = BTreeSet::new();

        while let Some(item) = worklist.pop_first() {
            if !already_processed.insert(item.clone()) {
                continue;
            }

            match item {
                WorkItem::Propagate {
                    factor,
                    dest,
                    transitive,
                } => {
                    let factor = self.resolve_vid(factor);
                    let dest = self.resolve_vid(dest);
                    if factor == dest {
                        continue;
                    }

                    // Check for existing edge
                    let existing_edge = self.divisibility_graph.find_edge(factor, dest);
                    let mut added_or_upgraded = false;

                    if let Some(edge_id) = existing_edge {
                        match self.divisibility_graph[edge_id] {
                            Direct | NotFactor => continue,
                            Transitive => {
                                if !transitive {
                                    self.divisibility_graph[edge_id] = Direct;
                                    added_or_upgraded = true;
                                }
                            }
                        }
                    } else {
                        // No edge exists - safe to add
                        self.divisibility_graph.add_edge(
                            factor,
                            dest,
                            if transitive { Transitive } else { Direct },
                        );
                        added_or_upgraded = true;
                    }

                    if added_or_upgraded {
                        // Anti-symmetry: if f | d and f != d, then d !| f
                        worklist.insert(WorkItem::RuleOut {
                            nonfactor: dest,
                            dest: factor,
                        });

                        // Positive propagation: if f | d and d | n, then f | n
                        for (neighbor, divisibility) in
                            neighbor_vids(&self.divisibility_graph, dest, Outgoing)
                        {
                            if neighbor == factor {
                                continue;
                            }
                            if matches!(divisibility, Direct | Transitive) {
                                worklist.insert(WorkItem::Propagate {
                                    factor,
                                    dest: neighbor,
                                    transitive: true,
                                });
                            }
                        }
                        // Rule 4: n !| d and f | d => n !| f
                        for (neighbor, divisibility) in
                            neighbor_vids(&self.divisibility_graph, dest, Incoming)
                        {
                            if neighbor == factor {
                                continue;
                            }
                            if divisibility == NotFactor {
                                worklist.insert(WorkItem::RuleOut {
                                    nonfactor: neighbor,
                                    dest: factor,
                                });
                            }
                        }
                        // Rule 3: f | d and f !| n => d !| n
                        for (neighbor, divisibility) in
                            neighbor_vids(&self.divisibility_graph, factor, Outgoing)
                        {
                            if neighbor == factor {
                                continue;
                            }
                            if divisibility == NotFactor {
                                worklist.insert(WorkItem::RuleOut {
                                    nonfactor: dest,
                                    dest: neighbor,
                                });
                            }
                        }
                        // Backward propagation: if A divides factor, and factor divides dest, then A divides dest
                        for (upstream, divisibility) in
                            neighbor_vids(&self.divisibility_graph, factor, Incoming)
                        {
                            if upstream == factor
                                || upstream == dest
                                || !matches!(divisibility, Direct | Transitive)
                            {
                                continue;
                            }
                            worklist.insert(WorkItem::Propagate {
                                factor: upstream,
                                dest,
                                transitive: true,
                            });
                        }
                    }
                }

                WorkItem::RuleOut { nonfactor, dest } => {
                    let nonfactor = self.resolve_vid(nonfactor);
                    let dest = self.resolve_vid(dest);
                    if nonfactor == dest || self.get_edge(nonfactor, dest).is_some() {
                        continue;
                    }

                    self.divisibility_graph.add_edge(nonfactor, dest, NotFactor);

                    for (neighbor, divisibility) in
                        neighbor_vids(&self.divisibility_graph, dest, Incoming)
                    {
                        if neighbor == nonfactor {
                            continue;
                        }
                        if matches!(divisibility, Direct | Transitive) {
                            // if nonfactor doesn't divide dest, then it also doesn't divide dest's factors
                            worklist.insert(WorkItem::RuleOut {
                                nonfactor,
                                dest: neighbor,
                            });
                        }
                    }
                }
            }
        }
    }
    pub fn is_known_factor(&mut self, factor_vid: VertexId, composite_vid: VertexId) -> bool {
        let factor_vid = self.resolve_vid(factor_vid);
        let composite_vid = self.resolve_vid(composite_vid);
        if factor_vid == composite_vid {
            return false;
        }

        // Check direct edge
        if let Some(edge) = self.get_edge(factor_vid, composite_vid) {
            return matches!(edge, Direct | Transitive);
        }

        spfa(&self.divisibility_graph, factor_vid, |edge| {
            if *edge.weight() == NotFactor {
                f64::INFINITY
            } else {
                0.0
            }
        })
        .unwrap()
        .distances[composite_vid.index()]
            == 0.0
    }

    pub fn merge_equivalent_expressions(
        &mut self,
        factor_vid: VertexId,
        equivalent: Factor,
        http: &impl FactorDbClient,
        check_factor_finder: bool,
    ) -> Vec<VertexId> {
        let factor_vid = self.resolve_vid(factor_vid);
        let current = self.get_factor(factor_vid);
        if equivalent == current {
            return vec![];
        }
        let existing_vid = self.vid_for_expr(&equivalent);
        if existing_vid == Some(factor_vid) {
            vec![]
        } else {
            info!("Merging equivalent expressions {current} and {equivalent}");
            let new_factor_vids = if let Some(existing_vid) = existing_vid {
                merge_vertices(self, http, factor_vid, existing_vid)
            } else {
                Vec::new()
            };
            // Update our reference to the vertex (it might have changed during merge)
            let new_vid = self.resolve_vid(factor_vid);
            if new_vid != factor_vid {
                // The original vertex was merged into another one
                return new_factor_vids;
            }
            let factor_vid = new_vid;
            self.vertex_id_by_expr
                .insert(equivalent.clone(), factor_vid);
            let current_len = if current.is_elided() {
                usize::MAX // replace elided numbers with full ones ASAP
            } else {
                current.to_unelided_string().len()
            };
            let mut new_factor_vids = if let Some(facts) =
                self.number_facts_map.get_mut(&factor_vid)
            {
                let (new_lower_bound_log10, new_upper_bound_log10) = estimate_log10(&equivalent);
                facts.lower_bound_log10 = facts.lower_bound_log10.max(new_lower_bound_log10);
                facts.upper_bound_log10 = facts.upper_bound_log10.min(new_upper_bound_log10);
                if check_factor_finder && !replace(&mut facts.checked_in_factor_finder, true) {
                    self.add_from_factor_finder(&current, http)
                } else {
                    Vec::new()
                }
            } else {
                error!("NumberFacts for {factor_vid:?} not found");
                Vec::new()
            };
            if check_factor_finder {
                new_factor_vids.extend(self.add_from_factor_finder(&equivalent, http));
            }
            if !equivalent.is_elided() && equivalent.to_unelided_string().len() < current_len {
                let _ = replace(
                    self.divisibility_graph.node_weight_mut(factor_vid).unwrap(),
                    equivalent,
                );
            }
            new_factor_vids
        }
    }

    fn add_from_factor_finder(
        &mut self,
        factor: &Factor,
        http: &impl FactorDbClient,
    ) -> Vec<VertexId> {
        find_unique_factors(factor)
            .into_iter()
            .filter_map(|new_factor| {
                let entry_id = http
                    .cached_factors(&Expression(Borrowed(&new_factor)))
                    .and_then(|f| f.id);
                let (vid, added) = add_factor_node(self, new_factor, entry_id, http);
                if added { Some(vid) } else { None }
            })
            .collect()
    }

    pub fn as_specifier(
        &mut self,
        factor_vid: VertexId,
        http: &impl FactorDbClient,
    ) -> NumberSpecifier<'_> {
        if let Some(facts) = self.facts(factor_vid)
            && let Some(factor_entry_id) = facts.entry_id
        {
            Id(factor_entry_id)
        } else {
            let factor = self.get_factor(factor_vid);
            http.cached_factors(&Expression(Borrowed(&factor)))
                .and_then(|f| f.id)
                .map(Id)
                .unwrap_or_else(|| Expression(Cow::Owned(factor)))
        }
    }
}

pub fn add_factor_node(
    data: &mut FactorData,
    factor: Factor,
    entry_id: Option<EntryId>,
    http: &impl FactorDbClient,
) -> (VertexId, bool) {
    let existing_vertex = data.vid_for_expr(&factor);
    let entry_id = entry_id.or_else(|| data.facts(existing_vertex?)?.entry_id);
    let cached_factors = entry_id
        .and_then(|entry_id| http.cached_factors(&Id(entry_id)))
        .or_else(|| http.cached_factors(&Expression(Borrowed(&factor))));
    let cached_entry_id = cached_factors.as_ref().and_then(|factors| factors.id);
    let entry_id = entry_id.or(cached_entry_id);
    let matching_vid = entry_id.and_then(|entry_id| data.vid_for_entry_id(entry_id));
    let (merge_dest, added) = existing_vertex
        .or(matching_vid)
        .map(|x| (x, false))
        .unwrap_or_else(|| {
            let factor_vid = data.divisibility_graph.add_node(factor.clone());
            data.vertex_id_by_expr.insert(factor.clone(), factor_vid);
            let (lower_bound_log10, upper_bound_log10) = estimate_log10(&factor);

            if let Some(entry_id) = entry_id {
                data.vertex_id_by_entry_id.insert(entry_id, factor_vid);
            }
            // Only full factorizations are stored in the cache or obtained via evaluate_as_numeric.
            let has_cached = cached_factors.is_some();
            data.number_facts_map.insert(
                factor_vid,
                NumberFacts {
                    last_known_status: None,
                    factors_known_to_factordb: NotUpToDate(vec![]),
                    numeric_value: evaluate_as_numeric(&factor),
                    lower_bound_log10,
                    upper_bound_log10,
                    entry_id,
                    checked_for_listed_algebraic: has_cached,
                    checked_in_factor_finder: has_cached,
                    expression_form_checked_in_factor_finder: has_cached,
                    checked_with_root_denominator: has_cached,
                },
            );

            if let Some(cached) = cached_factors {
                let mut cached_subfactors = Vec::with_capacity(cached.factors.len());
                for subfactor in cached.factors {
                    let (subfactor_vid, _) = if subfactor == factor {
                        (factor_vid, false)
                    } else {
                        let subfactor_entry_id = http
                            .cached_factors(&Expression(Borrowed(&subfactor)))
                            .and_then(|f| f.id);
                        add_factor_node(data, subfactor, subfactor_entry_id, http)
                    };
                    cached_subfactors.push(subfactor_vid);
                }
                let real_vid = data.resolve_vid(factor_vid);
                let facts = data.facts_mut(real_vid);
                facts.last_known_status = cached.status;
                facts.factors_known_to_factordb = UpToDate(cached_subfactors);
            }
            (factor_vid, true)
        });
    let mut merge_dest = data.resolve_vid(merge_dest);
    if data.get_factor(merge_dest) != factor {
        data.merge_equivalent_expressions(merge_dest, factor, http, true);
        merge_dest = data.resolve_vid(merge_dest);
    }
    if let Some(matching_vid) = matching_vid {
        let matching_vid = data.resolve_vid(matching_vid);
        if merge_dest != matching_vid {
            let new_vids = merge_vertices(data, http, merge_dest, matching_vid);
            // Merge any new factor vids found during the merge
            for vid in new_vids {
                let new_subfactor = data.get_factor(vid);
                let _ = add_factor_node(data, new_subfactor, None, http);
            }
        }
    }
    (merge_dest, added)
}

fn merge_vertices(
    data: &mut FactorData,
    http: &impl FactorDbClient,
    merge_dest: VertexId,
    matching_vid: VertexId,
) -> Vec<VertexId> {
    let merge_dest = data.resolve_vid(merge_dest);
    let matching_vid = data.resolve_vid(matching_vid);
    if merge_dest == matching_vid {
        return vec![];
    }
    // Check if we're already merging these vertices
    if data.deleted_synonyms.contains_key(&matching_vid) {
        return vec![]; // Already being merged
    }
    data.deleted_synonyms.insert(matching_vid, merge_dest);
    let mut worklist = BTreeSet::new();
    neighbor_vids(&data.divisibility_graph, matching_vid, Incoming)
        .into_iter()
        .for_each(|(neighbor_vid, divisibility)| {
            queue_transitive_divisibility(&mut worklist, neighbor_vid, merge_dest, divisibility)
        });
    neighbor_vids(&data.divisibility_graph, matching_vid, Outgoing)
        .into_iter()
        .for_each(|(neighbor_vid, divisibility)| {
            queue_transitive_divisibility(&mut worklist, merge_dest, neighbor_vid, divisibility)
        });
    data.process_divisibility_worklist(worklist);
    // Store whether we should run factor finder BEFORE we remove the vertex
    let should_run_factor_finder = data
        .number_facts_map
        .get(&matching_vid)
        .map(|facts| !facts.checked_in_factor_finder)
        .unwrap_or(false);

    // Transfer all edges from matching_vid to merge_dest

    // Destructure EdgeReference instances so they won't borrow the graph
    let edges_to_transfer: Vec<_> = data
        .divisibility_graph
        .edges_directed(matching_vid, Outgoing)
        .chain(
            data.divisibility_graph
                .edges_directed(matching_vid, Incoming),
        )
        .map(|edge| (edge.id(), edge.source(), edge.target(), *edge.weight()))
        .collect();

    for (edge_id, source, target, divisibility) in edges_to_transfer {
        // Skip self-edges
        if source == matching_vid && target == matching_vid {
            continue;
        }

        let new_source = if source == matching_vid {
            merge_dest
        } else {
            source
        };
        let new_target = if target == matching_vid {
            merge_dest
        } else {
            target
        };

        // Only add if edge doesn't already exist
        if data
            .divisibility_graph
            .find_edge(new_source, new_target)
            .is_none()
        {
            data.divisibility_graph
                .add_edge(new_source, new_target, divisibility);
        }
        data.divisibility_graph.remove_edge(edge_id);
    }

    // Remove the old vertex
    let old_factor_removed = data.divisibility_graph.remove_node(matching_vid);

    // Update mappings
    let old_factor = data.divisibility_graph[merge_dest].clone();
    data.vertex_id_by_expr.insert(old_factor, merge_dest);
    let mut checked_in_factor_finder = false;
    let mut new_factor_vids = Vec::new();
    if let Some(old_facts) = data.number_facts_map.remove(&matching_vid) {
        replace_with_or_abort(data.facts_mut(merge_dest), |facts| {
            checked_in_factor_finder =
                facts.checked_in_factor_finder && old_facts.checked_in_factor_finder;
            NumberFacts {
                lower_bound_log10: facts.lower_bound_log10.max(old_facts.lower_bound_log10),
                upper_bound_log10: facts.upper_bound_log10.min(old_facts.upper_bound_log10),
                numeric_value: facts.numeric_value.or(old_facts.numeric_value),
                entry_id: facts.entry_id.or(old_facts.entry_id),
                checked_for_listed_algebraic: facts.checked_for_listed_algebraic
                    && old_facts.checked_for_listed_algebraic,
                last_known_status: facts.last_known_status.max(old_facts.last_known_status),
                factors_known_to_factordb: NotUpToDate(
                    facts
                        .factors_known_to_factordb
                        .into_iter()
                        .chain(old_facts.factors_known_to_factordb)
                        .sorted_unstable()
                        .unique()
                        .collect(),
                ),
                checked_in_factor_finder,
                expression_form_checked_in_factor_finder: facts
                    .expression_form_checked_in_factor_finder
                    && old_facts.expression_form_checked_in_factor_finder,

                // root_denominator only has to be done with one or the other, because it doesn't depend
                // on the expression form among equivalents
                checked_with_root_denominator: facts.checked_with_root_denominator
                    || old_facts.checked_with_root_denominator,
            }
        });
    }
    if let Some(old_factor_removed) = old_factor_removed {
        // Update expression mapping
        data.vertex_id_by_expr
            .insert(old_factor_removed.clone(), merge_dest);

        // Check if we need to run factor finder on the old factor
        if should_run_factor_finder {
            new_factor_vids.extend(data.add_from_factor_finder(&old_factor_removed, http));
        }
        // Check if we should update the vertex's expression
        let current_factor = data.get_factor(merge_dest);
        if old_factor_removed != current_factor {
            let current_len = if current_factor.is_elided() {
                usize::MAX
            } else {
                current_factor.to_unelided_string().len()
            };

            if !old_factor_removed.is_elided()
                && old_factor_removed.to_unelided_string().len() < current_len
            {
                let _ = replace(
                    data.divisibility_graph.node_weight_mut(merge_dest).unwrap(),
                    old_factor_removed,
                );
            }
        }
    } else {
        error!(
            "Vertex {:?} was not found during merge_vertices",
            merge_dest
        );
    }

    new_factor_vids
}

fn queue_transitive_divisibility(
    worklist: &mut BTreeSet<WorkItem>,
    from: VertexId,
    to: VertexId,
    divisibility: Divisibility,
) {
    match divisibility {
        Direct => worklist.insert(WorkItem::Propagate {
            factor: from,
            dest: to,
            transitive: false,
        }),
        Transitive => worklist.insert(WorkItem::Propagate {
            factor: from,
            dest: to,
            transitive: true,
        }),
        NotFactor => worklist.insert(WorkItem::RuleOut {
            nonfactor: from,
            dest: to,
        }),
    };
}

fn neighbor_vids(
    divisibility_graph: &DivisibilityGraph,
    vertex_id: VertexId,
    direction: Direction,
) -> Vec<(VertexId, Divisibility)> {
    match direction {
        Outgoing => divisibility_graph
            .neighbors_directed(vertex_id, Outgoing)
            .map(|neighbor| {
                let edge = divisibility_graph.find_edge(vertex_id, neighbor).unwrap();
                (neighbor, divisibility_graph[edge])
            })
            .collect(),
        Incoming => divisibility_graph
            .neighbors_directed(vertex_id, Incoming)
            .map(|neighbor| {
                let edge = divisibility_graph.find_edge(neighbor, vertex_id).unwrap();
                (neighbor, divisibility_graph[edge])
            })
            .collect(),
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FactorsKnownToFactorDb {
    NotUpToDate(Vec<VertexId>),
    UpToDate(Vec<VertexId>),
}

impl IntoIterator for FactorsKnownToFactorDb {
    type Item = VertexId;
    type IntoIter = IntoIter<VertexId>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            NotUpToDate(f) | UpToDate(f) => f,
        }
        .into_iter()
    }
}

impl FactorsKnownToFactorDb {
    fn needs_update(&self) -> bool {
        match self {
            UpToDate(_) => false,
            NotUpToDate(_) => true,
        }
    }
}

#[derive(Debug)]
pub struct NumberFacts {
    last_known_status: Option<NumberStatus>,
    factors_known_to_factordb: FactorsKnownToFactorDb,
    numeric_value: Option<NumericFactor>,
    lower_bound_log10: NumberLength,
    upper_bound_log10: NumberLength,
    pub(crate) entry_id: Option<EntryId>,
    checked_for_listed_algebraic: bool,
    checked_in_factor_finder: bool,
    expression_form_checked_in_factor_finder: bool,
    checked_with_root_denominator: bool,
}

impl PartialEq<Self> for NumberFacts {
    fn eq(&self, other: &Self) -> bool {
        if let Some(entry_id) = self.entry_id
            && other.entry_id == Some(entry_id)
        {
            true
        } else {
            self.factors_known_to_factordb == other.factors_known_to_factordb
        }
    }
}

impl NumberFacts {
    #[inline(always)]
    pub(crate) fn is_known_finished(&self) -> bool {
        self.last_known_status.is_known_finished()
    }
    #[inline(always)]
    pub(crate) fn is_final(&self) -> bool {
        self.is_known_finished() && !self.needs_update()
    }
    #[inline(always)]
    pub(crate) fn needs_update(&self) -> bool {
        self.factors_known_to_factordb.needs_update()
    }

    /// True if add_factors_to_graph won't do anything (other than pick up factors someone else has
    /// submitted).
    #[inline(always)]
    pub(crate) fn is_fully_processed(&self) -> bool {
        !self.needs_update()
            && self.checked_for_listed_algebraic
            && self.expression_form_checked_in_factor_finder
            && self.checked_in_factor_finder
    }
}

#[inline(always)]
fn dedup_and_shuffle<T: Ord>(deque: &mut VecDeque<T>) {
    let deque_as_set = BTreeSet::from_iter(deque.drain(..));
    deque.extend(deque_as_set);
    deque.make_contiguous().shuffle(&mut rng());
}

#[framed]
pub async fn find_and_submit_factors(
    http: &impl FactorDbClientReadIdsAndExprs,
    id: EntryId,
    root_factor: Factor,
    skip_looking_up_known: bool,
) -> bool {
    let mut digits_or_expr_full = Vec::new();
    let mut data = FactorData::default();
    let elided = root_factor.is_elided();
    let (mut root_vid, _) = add_factor_node(&mut data, root_factor, Some(id), http);
    let mut factor_found = false;
    if (!skip_looking_up_known) || elided {
        let ProcessedStatusApiResponse {
            factors: known_factors,
            status,
            ..
        } = http.known_factors_as_digits(Id(id), false, true).await;
        if status.is_known_finished() {
            warn!("{id}: Already fully factored");
            return true;
        }
        if known_factors.len() == 1 && status != Some(PartlyFactoredComposite) {
            factor_found |= !data
                .merge_equivalent_expressions(
                    root_vid,
                    known_factors.into_iter().next().unwrap(),
                    http,
                    true,
                )
                .is_empty();
        } else {
            let root_factors: Vec<_> = known_factors
                .into_iter()
                .map(|known_factor| {
                    let entry_id = http
                        .cached_factors(&Expression(Borrowed(&known_factor)))
                        .and_then(|f| f.id);
                    let (factor_vid, added) =
                        add_factor_node(&mut data, known_factor, entry_id, http);
                    if added {
                        data.propagate_divisibility(factor_vid, root_vid, false);
                        digits_or_expr_full.push(factor_vid);
                    }
                    factor_vid
                })
                .collect();
            let root_facts = data.facts_mut(root_vid);
            root_facts.factors_known_to_factordb = match root_factors.len() {
                0 => NotUpToDate(vec![]),
                1 => {
                    if status.is_none_or(|status| status == PartlyFactoredComposite) {
                        NotUpToDate(root_factors)
                    } else {
                        UpToDate(root_factors)
                    }
                }
                _ => UpToDate(root_factors),
            }
        }
        let root_facts = data.facts_mut(root_vid);
        root_facts.last_known_status = status;
    } else {
        let root_facts = data.facts_mut(root_vid);
        root_facts.factors_known_to_factordb = UpToDate(vec![root_vid]);
        root_facts.last_known_status = Some(UnfactoredComposite);
    }
    let root_factor = data.get_factor(root_vid);
    debug!("{id}: Root node for {root_factor} has vertex ID {root_vid:?}",);
    digits_or_expr_full.push(root_vid);
    let mut accepted_factors = 0;
    let mut any_unprocessed = false;
    for factor_vid in digits_or_expr_full.into_iter().rev() {
        let factor_vid = data.resolve_vid(factor_vid);
        factor_found |= !add_factors_to_graph(http, &mut data, factor_vid)
            .await
            .is_empty();
        let factor_vid = data.resolve_vid(factor_vid);
        any_unprocessed |= !data
            .number_facts_map
            .get(&factor_vid)
            .unwrap()
            .is_fully_processed();
    }
    if !factor_found && !any_unprocessed {
        info!("{id}: No factors to submit");
        return false;
    }
    // Simplest case: try submitting all factors as factors of the root
    let (root_denominator_terms, root_denominator) = if let Complex { inner: ref c, .. } =
        root_factor
        && let ComplexFactor::Divide {
            right, right_hash, ..
        } = &**c
    {
        let multiply = Complex {
            inner: Multiply {
                terms_hash: *right_hash,
                terms: right.clone(),
            }
            .into(),
            hash: OnceLock::new(),
        };
        (Some(right.clone()), Some(multiply))
    } else {
        (None, None)
    };
    let mut all_vids: BTreeSet<VertexId> = data.divisibility_graph.node_indices().collect();
    let mut known_factors: Vec<_> = all_vids
        .iter()
        .copied()
        .filter(|&v| v != root_vid)
        .collect();
    known_factors.shuffle(&mut rng());
    let mut known_factors = VecDeque::from(known_factors);
    let mut factors_to_submit_in_graph = VecDeque::new();
    while let Some(factor_vid) = known_factors.pop_front() {
        let factor = data.get_factor(factor_vid);
        debug!("{id}: Factor {factor} has vertex ID {factor_vid:?}");
        match data.get_edge(factor_vid, root_vid) {
            Some(Direct) | Some(Transitive) | Some(NotFactor) => {
                info!(
                    "{id}: Skipping {factor} because it's already known to be a factor of ID {id} (status: {:?})",
                    data.get_edge(factor_vid, root_vid)
                );
                // This has been submitted directly to the root already, so it's probably already been
                // factored out of all other divisors.
                continue;
            }
            _ => {}
        }
        if factor.is_elided() {
            // Can't submit a factor that we can't express, but
            // running add_factors_to_graph may provide an equivalent expression, else we can save
            // it in case we find out the ID later
            info!("{id}: Temporarily skipping {factor} because digits are missing");
            let factors_of_factor = add_factors_to_graph(http, &mut data, factor_vid).await;
            if !factors_of_factor.is_empty() {
                all_vids.extend(factors_of_factor.iter().copied());
                factors_to_submit_in_graph.extend(factors_of_factor);
                dedup_and_shuffle(&mut factors_to_submit_in_graph);
            }
            if !factors_to_submit_in_graph.contains(&factor_vid) {
                factors_to_submit_in_graph.push_back(factor_vid);
            }
            continue;
        }
        match http.try_report_factor(Id(id), &factor).await {
            AlreadyFullyFactored => return true,
            Accepted => {
                data.propagate_divisibility(factor_vid, root_vid, false);
                mark_stale(&mut data, root_vid, http);
                let new_root_factors = add_factors_to_graph(http, &mut data, root_vid).await;
                all_vids.extend(new_root_factors.iter().copied());
                accepted_factors += 1;
            }
            DoesNotDivide => {
                let subfactors = add_factors_to_graph(http, &mut data, factor_vid).await;
                let subfactors_found = !subfactors.is_empty();
                if subfactors_found {
                    all_vids.extend(subfactors.iter().copied());
                    factors_to_submit_in_graph.extend(subfactors);
                    dedup_and_shuffle(&mut factors_to_submit_in_graph);
                }
                if !subfactors_found && let Some(ref root_denominator) = root_denominator {
                    data.facts_mut(factor_vid).checked_with_root_denominator = true;
                    if root_denominator.may_be_proper_divisor_of(&factor) {
                        let divided = div_exact(&factor, root_denominator).unwrap_or_else(|| {
                            simplify_divide(&factor, root_denominator_terms.as_ref().unwrap())
                        });
                        if divided.may_be_proper_divisor_of(&root_factor) {
                            let (divided_vid, added) =
                                add_factor_node(&mut data, divided, None, http);
                            if added {
                                all_vids.insert(divided_vid);
                                factors_to_submit_in_graph.push_back(divided_vid);
                                // Don't apply this recursively, except when divided was already in
                                // the graph for another reason
                                data.facts_mut(divided_vid).checked_with_root_denominator = true;
                            }
                        }
                    }
                }
            }
            OtherError => {
                factors_to_submit_in_graph.push_back(factor_vid);
            }
        }
        root_vid = data.resolve_vid(root_vid);
    }
    if factors_to_submit_in_graph.is_empty() {
        info!("{id}: {accepted_factors} factors accepted in a single pass");
        return accepted_factors > 0;
    }

    // A submission failed retryably, so now it gets more complicated:
    // (1) We may have found a false factor, in which case we should try submitting factors of that
    //     false factor if there are any.
    // (2) The number may have exceeded the site's capacity because it has too many factors already
    //     known, in which case we should submit the remaining factors to the cofactors rather than
    //     directly to the root.
    // (3) If both (1) and (2) apply, then we may end up with a factor that's a factor of multiple
    //     cofactors, so we need to report it to *all* of them to ensure FactorDB knows its full
    //     exponent.
    let mut iters_without_progress = 0;
    let mut iters_to_next_report = 0;
    info!(
        "{id}: {} factors left to submit after first pass",
        factors_to_submit_in_graph.len()
    );
    'graph_iter: while !data
        .facts(root_vid)
        .expect("{id}: Reached 'graph_iter when root not entered in number_facts_map")
        .is_known_finished()
        && let node_count = data.divisibility_graph.node_count()
        && iters_without_progress < node_count * SUBMIT_FACTOR_MAX_ATTEMPTS
        && let Some(factor_vid) = factors_to_submit_in_graph.pop_front()
        && let edge_count = data.divisibility_graph.edge_count()
        && let complete_graph_edge_count = node_count * (node_count - 1)
        && edge_count < complete_graph_edge_count
    {
        if iters_to_next_report == 0 {
            iters_to_next_report = node_count.min(20);
            let (direct_divisors, non_factors) = data
                .divisibility_graph
                .edge_references()
                .map(|e| match *e.weight() {
                    Direct => (1, 0),
                    NotFactor => (0, 1),
                    _ => (0, 0),
                })
                .reduce(|(x1, y1), (x2, y2)| (x1 + x2, y1 + y2))
                .unwrap_or((0, 0));
            info!(
                "{id}: Divisibility graph has {node_count} vertices and {edge_count} edges \
            ({:.2}% fully connected). {direct_divisors} confirmed-known divides relations, \
            {non_factors} ruled out. \
        {accepted_factors} factors accepted so far. {} fully factored numbers. {} known entry IDs",
                edge_count as f64 * 100.0 / complete_graph_edge_count as f64,
                data.number_facts_map
                    .values()
                    .filter(|facts| facts.is_known_finished())
                    .count(),
                data.number_facts_map
                    .values()
                    .filter(|facts| facts.entry_id.is_some())
                    .count()
            );
        }
        iters_without_progress += 1;
        iters_to_next_report -= 1;
        // root can't be a factor of any other number we'll encounter
        data.rule_out_divisibility(root_vid, factor_vid);
        // elided numbers and numbers over 65500 digits without an expression form can only
        // be submitted as factors, even if their IDs are known
        // however, this doesn't affect the divisibility graph because the ID may be found
        // later
        let factor = data.get_factor(factor_vid);
        if factor.is_elided() {
            info!("{id}: Temporarily skipping {factor} because digits are missing");
            // Can't submit a factor that we can't express, but
            // running add_factors_to_graph may provide an equivalent expression, else we can save
            // it in case we find out the ID later
            let new_factors_of_factor = add_factors_to_graph(http, &mut data, factor_vid).await;
            if !new_factors_of_factor.is_empty() {
                factors_to_submit_in_graph.extend(new_factors_of_factor);
                dedup_and_shuffle(&mut factors_to_submit_in_graph);
            }
            if !factors_to_submit_in_graph.contains(&factor_vid) {
                factors_to_submit_in_graph.push_back(factor_vid);
            }
            continue;
        }
        let mut dest_factors = all_vids
            .iter()
            .copied()
            .filter(|&dest_vid|
                    // if this edge exists, FactorDB already knows whether factor is a factor of dest
                    dest_vid != factor_vid && data.get_edge(factor_vid, dest_vid).is_none())
            .collect::<Vec<_>>();
        dest_factors.shuffle(&mut rng());
        if dest_factors.is_empty() {
            info!("{id}: Skipping {factor} because there are no more cofactors it can divide");
            continue;
        };
        let mut put_factor_back_into_queue = false;
        'per_cofactor: for cofactor_vid in dest_factors.into_iter() {
            if factor_vid == cofactor_vid {
                error!("dest_factors included factor_vid");
                continue;
            }
            let cofactor = data.get_factor(cofactor_vid);
            if data.is_known_factor(factor_vid, cofactor_vid) {
                info!(
                    "{id}: Skipping submission of {factor} to {cofactor} because it's already known (based on graph check)"
                );
                // This factor already known.
                // If transitive, submit to a smaller cofactor instead.
                // If direct, nothing left to do.
                data.propagate_divisibility(factor_vid, cofactor_vid, true);
                continue;
            }
            let factor_facts = data.facts(factor_vid)
                .expect("{id}: Reached factors_known_to_factordb check for a number not entered in number_facts_map");
            if factor_facts.last_known_status == Some(Invalid) {
                info!("{id}: Skipping submission of {factor} because it's not an integer");
                continue 'graph_iter;
            }
            match factor_facts.factors_known_to_factordb {
                UpToDate(ref already_known_factors) | NotUpToDate(ref already_known_factors) => {
                    if already_known_factors.contains(&cofactor_vid) {
                        info!(
                            "{id}: Skipping submission of {factor} to {cofactor} because it's already known (based on FactorDB check)"
                        );
                        data.propagate_divisibility(cofactor_vid, factor_vid, false);
                        continue;
                    } else if data
                        .facts(cofactor_vid)
                        .expect("{id}: cofactor not in number_facts_map")
                        .is_known_finished()
                    {
                        debug!(
                            "{id}: Skipping submission of {factor} to {cofactor} because destination is already fully factored (based on FactorDB check)"
                        );
                        data.rule_out_divisibility(cofactor_vid, factor_vid);

                        continue;
                    }
                }
            }
            if factor == cofactor {
                warn!(
                    "{id}: Found duplicate vertices: {factor_vid:?} and {cofactor_vid:?} are both {factor}"
                );
                let new_vids = merge_vertices(&mut data, http, factor_vid, cofactor_vid);
                // Merge any new factor vids found during the merge
                for vid in new_vids {
                    let new_subfactor = data.get_factor(vid);
                    let _ = add_factor_node(&mut data, new_subfactor, None, http);
                }
                all_vids.remove(&cofactor_vid);
                continue;
            }
            if !factor.may_be_proper_divisor_of(&cofactor) {
                data.rule_out_divisibility(factor_vid, cofactor_vid);
                if cofactor_vid == root_vid {
                    continue 'graph_iter; // Skip put_factor_back_in_queue check
                }
                continue;
            }
            // NumericFactor entries are already fully factored
            if let Numeric(_) = cofactor {
                debug!(
                    "{id}: Skipping submission of {factor} to {cofactor} because the destination is too small"
                );
                continue;
            }
            let cofactor_facts = data.facts(cofactor_vid).expect(
                "{id}: Reached cofactor_facts check for a number not entered in number_facts_map",
            );
            if cofactor_facts.last_known_status == Some(Invalid) {
                for factor_vid in data.divisibility_graph.node_indices().collect::<Vec<_>>().into_iter() {
                    data.rule_out_divisibility(factor_vid, cofactor_vid);
                    data.rule_out_divisibility(cofactor_vid, factor_vid);
                }
                info!(
                    "{id}: Skipping submission of {factor} to {cofactor} because the destination is not an integer"
                );
                continue;
            }
            let cofactor_upper_bound_log10 = cofactor_facts.upper_bound_log10;
            let known_factor_vids = match cofactor_facts.factors_known_to_factordb {
                UpToDate(ref vids) | NotUpToDate(ref vids) if !vids.is_empty() => {
                    Some(vids.clone())
                }
                _ => None,
            };
            if let Some(known_factor_vids) = known_factor_vids {
                let mut by_status = known_factor_vids
                    .into_iter()
                    .filter_map(|known_factor_vid| {
                        if data.get_edge(factor_vid, known_factor_vid) != Some(NotFactor) {
                            None
                        } else if factor.may_be_proper_divisor_of(&data.get_factor(known_factor_vid)) && cofactor_upper_bound_log10
                            >= data.facts(known_factor_vid)
                            .expect("{id}: known_factor_statuses included a number not entered in number_facts_map")
                            .lower_bound_log10 {
                            // possible that cofactor == known_factor * x == factor * x * y
                            Some((true, known_factor_vid))
                        } else {
                            Some((false, known_factor_vid))
                        }
                    })
                    .into_group_map();
                let possible_factors = by_status.remove(&true).unwrap_or(vec![]);
                let unknown_non_factors = by_status.remove(&false).unwrap_or(vec![]);
                drop(by_status);
                if possible_factors.is_empty() {
                    info!(
                        "{id}: Skipping submission of {factor} to {cofactor} because it can't divide any of the remaining cofactors (based on FactorDB check)"
                    );
                    // No possible path from factor to cofactor
                    for unknown_non_factor in unknown_non_factors {
                        data.rule_out_divisibility(factor_vid, unknown_non_factor);
                    }
                    data.rule_out_divisibility(factor_vid, cofactor_vid);
                    let factors_to_submit_instead =
                        add_factors_to_graph(http, &mut data, factor_vid).await;
                    if !factors_to_submit_instead.is_empty() {
                        all_vids.extend(factors_to_submit_instead.iter().copied());
                        factors_to_submit_in_graph.extend(factors_to_submit_instead);
                        dedup_and_shuffle(&mut factors_to_submit_in_graph);
                    }
                    continue;
                } else if possible_factors.into_iter().all(|possible_factor_vid| {
                    data.get_edge(factor_vid, possible_factor_vid) == Some(Direct)
                }) {
                    info!(
                        "{id}: Skipping submission of {factor} to {cofactor} because it's already known (based on graph check)"
                    );
                    // Submit to one of the known_factors instead
                    data.propagate_divisibility(factor_vid, cofactor_vid, true);
                    continue;
                }
            }
            let factor_facts = data.facts(factor_vid)
                .expect("{id}: Reached factors_known_to_factordb check for a number not entered in number_facts_map");
            let factor_is_prime = factor_facts.last_known_status == Some(Prime);
            let factor_lower_bound_log10 = factor_facts.lower_bound_log10;
            if factor_is_prime {
                let cofactor_vid = data.resolve_vid(cofactor_vid);
                let cofactor_prime_factor_log10s =
                    neighbor_vids(&data.divisibility_graph, cofactor_vid, Incoming)
                        .into_iter()
                        .filter(|(_, divisibility)| *divisibility != NotFactor)
                        .filter_map(|(neighbor_vid, _)| {
                            let facts = data.facts(neighbor_vid).unwrap();
                            if facts.last_known_status == Some(Prime) {
                                Some(facts.lower_bound_log10)
                            } else {
                                None
                            }
                        })
                        .sum();
                let cofactor_remaining_factors_upper_bound_log10 =
                    cofactor_upper_bound_log10.saturating_sub(cofactor_prime_factor_log10s);
                if factor_lower_bound_log10 > cofactor_remaining_factors_upper_bound_log10 {
                    info!(
                        "{id}: Skipping submission of {factor} to {cofactor} because it's too large to divide any of the remaining cofactors (based on previous submissions)"
                    );
                    data.rule_out_divisibility(factor_vid, cofactor_vid);
                    if cofactor_vid == root_vid {
                        continue 'graph_iter; // Skip put_factor_back_in_queue check
                    }
                    continue;
                }
            }
            if data.is_known_factor(cofactor_vid, factor_vid) {
                // factor is transitively divisible by cofactor
                info!(
                    "{id}: Skipping submission of {factor} to {cofactor} because it's a multiple"
                );
                data.propagate_divisibility(cofactor_vid, factor_vid, true);
                continue;
            }
            // elided numbers can only be used as dests if their IDs are known
            // however, this doesn't affect the divisibility graph because the ID may be found
            // later
            if cofactor.is_elided()
                && data.facts(cofactor_vid)
                .expect(
                    "{id}: Tried to check for entry_id for a cofactor not entered in number_facts_map",
                )
                .entry_id
                .is_none()
            {
                info!(
                    "{id}: Temporarily skipping submission of {factor} to {cofactor} because we can't unambiguously identify the destination"
                );

                // Running add_factors_to_graph may yield an equivalent expression
                let new_factors_of_cofactor = add_factors_to_graph(http, &mut data, cofactor_vid).await;
                if !new_factors_of_cofactor.is_empty() {
                    all_vids.extend(new_factors_of_cofactor.iter().copied());
                    factors_to_submit_in_graph
                        .extend(new_factors_of_cofactor);
                    dedup_and_shuffle(&mut factors_to_submit_in_graph);
                }
                put_factor_back_into_queue = true;
                break 'per_cofactor;
            }
            let cofactor_specifier = data.as_specifier(cofactor_vid, http);
            match http.try_report_factor(cofactor_specifier, &factor).await {
                AlreadyFullyFactored => {
                    if cofactor_vid == root_vid {
                        warn!("{id}: Already fully factored");
                        return true;
                    }
                    mark_fully_factored(cofactor_vid, &mut data);
                    continue;
                }
                Accepted => {
                    data.propagate_divisibility(factor_vid, cofactor_vid, false);
                    mark_stale(&mut data, cofactor_vid, http);
                    accepted_factors += 1;
                    iters_without_progress = 0;
                    // Move newly-accepted factor to the back of the list
                    if cofactor_vid == root_vid || cofactor_upper_bound_log10 >= 50000 {
                        let new_root_factors =
                            add_factors_to_graph(http, &mut data, root_vid).await;
                        all_vids.extend(new_root_factors.iter().copied());
                        // skip put_factor_back_into_queue check
                        continue 'graph_iter;
                    }
                    put_factor_back_into_queue = true;
                    break 'per_cofactor;
                }
                DoesNotDivide => {
                    data.rule_out_divisibility(factor_vid, cofactor_vid);
                    let subfactors = add_factors_to_graph(http, &mut data, factor_vid).await;
                    if !subfactors.is_empty() {
                        all_vids.extend(subfactors.iter().copied());
                        factors_to_submit_in_graph.extend(subfactors);
                        dedup_and_shuffle(&mut factors_to_submit_in_graph);
                    } else if let Some(ref root_denominator) = root_denominator {
                        let facts = data.facts_mut(factor_vid);
                        if !replace(&mut facts.checked_with_root_denominator, true)
                            && root_denominator.may_be_proper_divisor_of(&factor)
                        {
                            let divided =
                                div_exact(&factor, root_denominator).unwrap_or_else(|| {
                                    simplify_divide(
                                        &factor,
                                        root_denominator_terms.as_ref().unwrap(),
                                    )
                                });
                            if divided.may_be_proper_divisor_of(&root_factor) {
                                let (divided_vid, added) =
                                    add_factor_node(&mut data, divided, None, http);
                                if added {
                                    all_vids.insert(divided_vid);
                                    factors_to_submit_in_graph.push_back(divided_vid);
                                    // Don't apply this recursively, except when divided was already in
                                    // the graph for another reason
                                    data.facts_mut(divided_vid).checked_with_root_denominator =
                                        true;
                                }
                            }
                        }
                    }
                    if cofactor_vid == root_vid {
                        continue 'graph_iter; // Skip put_factor_back_into_queue check for factors that don't divide the root
                    } else {
                        let cofactor_facts = data.facts(cofactor_vid)
                            .expect("{id}: Tried to fetch cofactor_facts for a cofactor not entered in number_facts_map");
                        if cofactor_facts.needs_update()
                            || !cofactor_facts.checked_for_listed_algebraic
                        {
                            // An error must have occurred while fetching cofactor's factors
                            put_factor_back_into_queue = true;
                        }
                    }
                }
                OtherError => {
                    put_factor_back_into_queue = true;
                    let new_cofactor_factors =
                        add_factors_to_graph(http, &mut data, cofactor_vid).await;
                    if !new_cofactor_factors.is_empty() {
                        all_vids.extend(new_cofactor_factors.iter().copied());
                        iters_without_progress = 0;
                    }
                }
            }
        }
        if put_factor_back_into_queue && !factors_to_submit_in_graph.contains(&factor_vid) {
            factors_to_submit_in_graph.push_back(factor_vid);
        }
    }

    for factor_vid in all_vids.iter().copied().filter(|&v| v != root_vid) {
        let factor = data.get_factor(factor_vid);
        if factor.is_elided() {
            debug!(
                "{id}: Skipping writing {factor} to failed-submission file because we don't know its specifier"
            );
            continue;
        }
        let factor = factor.to_unelided_string();
        if data.is_known_factor(factor_vid, root_vid) {
            continue;
        }
        match FAILED_U_SUBMISSIONS_OUT
            .get()
            .unwrap()
            .lock()
            .await
            .write_fmt(format_args!("{id},{factor}\n"))
        {
            Ok(_) => warn!("{id}: wrote {} to failed submissions file", factor),
            Err(e) => error!(
                "{id}: failed to write {} to failed submissions file: {e}",
                factor
            ),
        }
    }
    accepted_factors > 0
}

#[inline(always)]
fn mark_stale(data: &mut FactorData, stale_vid: VertexId, http: &impl FactorDbClient) {
    let entry_id = data.facts(stale_vid).unwrap().entry_id;
    let expression = data.get_factor(stale_vid);
    replace_with_or_abort(data.facts_mut(stale_vid), |facts| {
        if !facts.is_final()
            && let UpToDate(factors) = facts.factors_known_to_factordb
        {
            NumberFacts {
                factors_known_to_factordb: NotUpToDate(factors),
                ..facts
            }
        } else {
            facts
        }
    });
    http.invalidate_cached_factors(entry_id, &expression);
}

fn mark_fully_factored(vid: VertexId, data: &mut FactorData) {
    let mut worklist = BTreeSet::new();
    mark_fully_factored_internal(vid, data, &mut worklist);
    data.process_divisibility_worklist(worklist);
}

fn mark_fully_factored_internal(
    mut vid: VertexId,
    data: &mut FactorData,
    worklist: &mut BTreeSet<WorkItem>,
) {
    let facts = data.facts_mut(vid);
    if facts.is_known_finished() {
        return;
    }
    facts.checked_for_listed_algebraic = true;
    facts.checked_in_factor_finder = true;
    facts.expression_form_checked_in_factor_finder = true;
    facts.checked_with_root_denominator = true;
    let no_other_factors = if let UpToDate(factors) = &facts.factors_known_to_factordb {
        if factors.len() == 1 {
            facts.last_known_status = Some(Prime);
        } else {
            facts.last_known_status = Some(FullyFactored);
            for neighbor in factors.clone() {
                let neighbor_facts = data.facts_mut(neighbor);
                neighbor_facts.factors_known_to_factordb = UpToDate(vec![neighbor]);
                neighbor_facts.last_known_status = Some(Prime);
                worklist.insert(WorkItem::Propagate {
                    factor: neighbor,
                    dest: vid,
                    transitive: false,
                });
            }
        }
        true
    } else {
        facts.last_known_status = Some(FullyFactored);
        false
    };

    // Recursively mark all known factors as fully factored
    for other_factor_vid in data
        .divisibility_graph
        .node_indices()
        .filter(|factor_vid| *factor_vid != vid)
        .collect::<Vec<_>>()
        .into_iter()
    {
        match data.get_edge(other_factor_vid, vid) {
            Some(Direct | Transitive) => {
                mark_fully_factored_internal(other_factor_vid, data, worklist);
                vid = data.resolve_vid(vid);
            }
            None if no_other_factors => {
                worklist.insert(WorkItem::RuleOut {
                    nonfactor: other_factor_vid,
                    dest: vid,
                });
            }
            _ => {}
        }
    }
}

#[framed]
async fn add_factors_to_graph(
    http: &impl FactorDbClientReadIdsAndExprs,
    data: &mut FactorData,
    factor_vid: VertexId,
) -> Box<[VertexId]> {
    let (mut id, needs_update) = {
        let facts = data.facts(factor_vid).expect(
            "add_factors_to_graph called on a number that's not entered in number_facts_map",
        );
        (facts.entry_id, facts.needs_update())
    };
    let mut added = BTreeSet::new();
    let factor = data.get_factor(factor_vid);
    let elided = factor.is_elided();
    // First, check factordb.com/api for already-known factors
    if needs_update || elided {
        let factor_specifier = data.as_specifier(factor_vid, http);
        let ProcessedStatusApiResponse {
            status,
            factors: known_factors,
            id: new_id,
        } = http
            .known_factors_as_digits(factor_specifier, true, elided)
            .await;
        let known_factor_count = known_factors.len();
        let new_known_factors: Vec<_> = if known_factor_count == 1 {
            let known_factor = known_factors.into_iter().next().unwrap();
            if known_factor != factor {
                data.merge_equivalent_expressions(factor_vid, known_factor, http, true);
            }
            vec![factor_vid]
        } else {
            known_factors
                .into_iter()
                .map(|known_factor| {
                    let entry_id = http
                        .cached_factors(&Expression(Borrowed(&known_factor)))
                        .and_then(|f| f.id);
                    let (known_factor_vid, is_new) =
                        add_factor_node(data, known_factor, entry_id, http);
                    data.propagate_divisibility(known_factor_vid, factor_vid, false);
                    if is_new {
                        added.insert(known_factor_vid);
                    }
                    known_factor_vid
                })
                .collect()
        };
        let facts = data.facts_mut(factor_vid);
        if known_factor_count > 0 {
            facts.factors_known_to_factordb = UpToDate(new_known_factors);
        }
        facts.entry_id = facts.entry_id.or(new_id);
        id = facts.entry_id;
        if let Some(status) = status {
            facts.last_known_status = Some(status);
            if status == Prime || status == FullyFactored {
                mark_fully_factored(factor_vid, data);
            }
        }
        if let Some(id) = id {
            data.vertex_id_by_entry_id.insert(id, factor_vid);
        }
    }

    // Next, check factordb.com/frame_moreinfo.php for listed algebraic factors
    let facts = data.facts_mut(factor_vid);
    if let Some(id) = id
        && !facts.checked_for_listed_algebraic
    {
        if let Some(known_id) = http
            .cached_factors(&Expression(Borrowed(&factor)))
            .and_then(|f| f.id)
            && id != known_id
        {
            error!("Tried to look up {factor} using a smaller number's id {id}");
        } else {
            info!("{id}: Checking for listed algebraic factors");
            // Links before the "Is factor of" header are algebraic factors; links after it aren't
            let url = format!("https://factordb.com/frame_moreinfo.php?id={id}");
            let result = http.try_get_and_decode(&url).await;
            if let Some(result) = result
                && let Some((_before, listed_algebraic_and_rest)) =
                    result.split_once("Algebraic factors")
                && let Some((listed_algebraic, _rest)) =
                    listed_algebraic_and_rest.split_once("Is factor of")
            {
                facts.checked_for_listed_algebraic = true;
                let algebraic_factors = http.read_ids_and_exprs(&listed_algebraic);
                for (subfactor_entry_id, factor_digits_or_expr) in algebraic_factors {
                    let subfactor = Factor::from(factor_digits_or_expr);
                    let (subfactor_vid, is_new) =
                        add_factor_node(data, subfactor, Some(subfactor_entry_id), http);
                    if is_new {
                        added.insert(subfactor_vid);
                    }
                }
            } else {
                error!("{id}: Failed to decode algebraic-factor list");
            }
        }
    }

    // Next, check if factor_finder can find factors
    let facts = data.facts_mut(factor_vid);
    if !replace(&mut facts.checked_in_factor_finder, true) {
        added.extend(data.add_from_factor_finder(&factor, http));
    }
    let facts = data.facts_mut(factor_vid);
    if let Some(entry_id) = facts.entry_id
        && !facts.expression_form_checked_in_factor_finder
        && let Some(expression_form) = http.try_get_expression_form(entry_id).await
    {
        facts.expression_form_checked_in_factor_finder = true;
        if expression_form != factor {
            let added_via_equiv =
                data.merge_equivalent_expressions(factor_vid, expression_form.clone(), http, true);
            added.extend(added_via_equiv);
        }
    }

    added.into_iter().collect()
}

#[cfg(test)]
pub mod tests {
    use crate::GLOBAL;
    use rand::Rng;
    use rand::rng;
    use std::env::temp_dir;
    use std::fs::File;
    use std::hint::black_box;
    use std::iter::{once, repeat};
    use sysinfo::{MemoryRefreshKind, RefreshKind};

    use crate::ReportFactorResult;
    use crate::algebraic::Factor;
    use crate::graph::{EntryId, NumericFactor};
    use crate::graph::{FactorData, add_factor_node, find_and_submit_factors};
    use crate::net::NumberStatus::Unknown;
    use crate::net::{
        FactorDbClientReadIdsAndExprs, MockFactorDbClient, ProcessedStatusApiResponse,
    };
    use crate::{FAILED_U_SUBMISSIONS_OUT, log_stats};
    use const_format::formatcp;
    use hipstr::HipStr;
    use mockall::predicate::eq;
    use nonzero::nonzero;
    use tokio::sync::Mutex;

    #[test]
    fn test_is_known_factor_numeric() {
        use crate::net::MockFactorDbClient;
        let mut http = MockFactorDbClient::new();
        http.expect_known_factors_as_digits().never();
        http.expect_cached_factors().return_const(None);
        http.expect_wait_if_resource_limited().never();
        http.expect_report_numeric_factor().never();
        http.expect_retrying_get_and_decode().never();
        http.expect_try_get_and_decode().never();
        http.expect_try_get_expression_form().never();
        http.expect_try_report_factor().never();

        let mut data = FactorData::default();
        let (node1, added) = add_factor_node(&mut data, Factor::from("2^16-1"), None, &http);
        assert!(added);
        let (node2, added) = add_factor_node(&mut data, Factor::from("2^8-1"), None, &http);
        assert!(added);
        let (node3, added) = add_factor_node(&mut data, Factor::from("2^4-1"), None, &http);
        assert!(added);
        let (node4, added) = add_factor_node(&mut data, Factor::from("2^4+1"), None, &http);
        assert!(added);
        let (node5, added) = add_factor_node(&mut data, Factor::from("2^8+1"), None, &http);
        assert!(added);
        drop(http);
        data.propagate_divisibility(node2, node1, false);
        data.propagate_divisibility(node3, node2, false);
        data.propagate_divisibility(node4, node2, false);
        data.propagate_divisibility(node5, node1, false);
        assert!(!data.is_known_factor(node1, node1));
        assert!(data.is_known_factor(node2, node1));
        assert!(data.is_known_factor(node3, node1));
        assert!(data.is_known_factor(node4, node1));
        assert!(data.is_known_factor(node5, node1));
        assert!(!data.is_known_factor(node1, node2));
        assert!(!data.is_known_factor(node2, node2));
        assert!(data.is_known_factor(node3, node2));
        assert!(data.is_known_factor(node4, node2));
        for divisibility_leaf in [node3, node4, node5] {
            for other_node in [node1, node2, node3, node4, node5] {
                assert!(!data.is_known_factor(other_node, divisibility_leaf));
            }
        }
    }

    #[test]
    fn test_is_known_factor() {
        use crate::net::MockFactorDbClient;
        let mut http = MockFactorDbClient::new();
        http.expect_known_factors_as_digits().never();
        http.expect_cached_factors().return_const(None);
        http.expect_wait_if_resource_limited().never();
        http.expect_report_numeric_factor().never();
        http.expect_retrying_get_and_decode().never();
        http.expect_try_get_and_decode().never();
        http.expect_try_get_expression_form().never();
        http.expect_try_report_factor().never();

        const LARGE_PRIME: NumericFactor = 340282366920938463463374607431768211297; // last prime below 2^128

        let mut data = FactorData::default();
        let (node1, added) = add_factor_node(
            &mut data,
            Factor::from(format!("{LARGE_PRIME}^16-1").as_str()),
            None,
            &http,
        );
        assert!(added);
        let (node2, added) = add_factor_node(
            &mut data,
            Factor::from(format!("{LARGE_PRIME}^8-1").as_str()),
            None,
            &http,
        );
        assert!(added);
        let (node3, added) = add_factor_node(
            &mut data,
            Factor::from(format!("{LARGE_PRIME}^4-1").as_str()),
            None,
            &http,
        );
        assert!(added);
        let (node4, added) = add_factor_node(
            &mut data,
            Factor::from(format!("{LARGE_PRIME}^4+1").as_str()),
            None,
            &http,
        );
        assert!(added);
        let (node5, added) = add_factor_node(
            &mut data,
            Factor::from(format!("{LARGE_PRIME}^8+1").as_str()),
            None,
            &http,
        );
        assert!(added);
        drop(http);
        data.propagate_divisibility(node2, node1, false);
        data.propagate_divisibility(node3, node2, false);
        data.propagate_divisibility(node4, node2, false);
        data.propagate_divisibility(node5, node1, false);
        assert!(!data.is_known_factor(node1, node1));
        assert!(data.is_known_factor(node2, node1));
        assert!(data.is_known_factor(node3, node1));
        assert!(data.is_known_factor(node4, node1));
        assert!(data.is_known_factor(node5, node1));
        assert!(!data.is_known_factor(node1, node2));
        assert!(!data.is_known_factor(node2, node2));
        assert!(data.is_known_factor(node3, node2));
        assert!(data.is_known_factor(node4, node2));
        for divisibility_leaf in [node3, node4, node5] {
            for other_node in [node1, node2, node3, node4, node5] {
                assert!(!data.is_known_factor(other_node, divisibility_leaf));
            }
        }
    }

    #[ignore]
    #[test]
    fn test_find_and_submit() {
        use crate::RealFactorDbClient;
        use tokio::runtime::Runtime;
        use tokio::sync::Mutex;

        simple_log::console("info").unwrap();
        let runtime = Runtime::new().unwrap();
        runtime.block_on(async {
            FAILED_U_SUBMISSIONS_OUT
                .get_or_init(async || {
                    Mutex::new(
                        File::create_new(temp_dir().join(rng().next_u64().to_string())).unwrap(),
                    )
                })
                .await;
            let mut http = RealFactorDbClient::new(nonzero!(10_000u32));
            find_and_submit_factors(
                &mut http,
                11_000_000_004_420_33401,
                format!("I({})", 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19).into(),
                false,
            )
            .await
        });
        runtime.shutdown_background();
    }

    #[test]
    fn test_merge_equivalent_expressions_infinite_recursion_2025_12_12() {
        let mut http = MockFactorDbClient::new();
        http.expect_known_factors_as_digits().never();
        http.expect_cached_factors().return_const(None);
        http.expect_wait_if_resource_limited().never();
        http.expect_report_numeric_factor().never();
        http.expect_retrying_get_and_decode().never();
        http.expect_try_get_and_decode().never();
        http.expect_try_get_expression_form().never();
        http.expect_try_report_factor().never();

        let mut data = FactorData::default();
        let (root_vid, added) = add_factor_node(
            &mut data,
            Factor::from("(10^65035*18+10^130071-1)/9"),
            None,
            &http,
        );
        assert!(added);
        data.merge_equivalent_expressions(
            root_vid,
            Factor::from("(10^65035*18+10^130071-1)/3^2"),
            &http,
            true,
        );
    }

    #[test]
    fn test_add_factor_node_deduplication() {
        let mut http = MockFactorDbClient::new();
        http.expect_cached_factors().return_const(None);
        // Add minimal expectations for unused methods to satisfy mocker if needed, though 'never()' is default
        let mut data = FactorData::default();

        let factor = Factor::from("2^32+1");
        let (vid1, added1) = add_factor_node(&mut data, factor.clone(), None, &http);
        assert!(added1);

        let (vid2, added2) = add_factor_node(&mut data, factor, None, &http);
        assert!(!added2);
        assert_eq!(vid1, vid2);
    }

    #[test]
    fn test_merge_equivalent_expressions_logic() {
        let mut http = MockFactorDbClient::new();
        http.expect_cached_factors().return_const(None);
        http.expect_known_factors_as_digits().never();

        let mut data = FactorData::default();

        // Create two nodes that are effectively the same but added differently
        let f1 = Factor::from("2^32+1");
        let f2 = Factor::from("4294967297"); // 2^32+1 evaluated

        let (_vid1, _) = add_factor_node(&mut data, f1.clone(), None, &http);
        let (_vid2, _) = add_factor_node(&mut data, f2.clone(), None, &http);

        // Initially they might be separate if not using canonical forms or if forced separately
        // But add_factor_node checks numeric value cache, so they MIGHT be merged automatically if they evaluate to same numeric
        // To force them separate for this test, let's use symbolic expressions that don't immediately simplify/evaluate to same
        // But `merge_equivalent_expressions` is explicitly for this.

        // Retrying with symbolic that won't auto-merge
        let f3 = Factor::from("x+y");
        let f4 = Factor::from("y+x"); // commuted

        let (_vid3, _) = add_factor_node(&mut data, f3, None, &http);
        let (_vid4, _) = add_factor_node(&mut data, f4.clone(), None, &http);

        // Assert they are different initially if our hash/eq logic relies on structure (which it does mostly, though We have some commutativity tests)
        // Actually, our Factor::eq handles commutativity for AddSub, so they might be deduplicated already!
        // Let's use something that isn't automatically deduplicated but IS equivalent.
        // e.g. x+x and 2*x

        let f5 = Factor::from("a+a");
        let f6 = Factor::from("2*a");

        let (vid5, _) = add_factor_node(&mut data, f5, None, &http);
        let (vid6, _) = add_factor_node(&mut data, f6.clone(), None, &http);

        assert_ne!(vid5, vid6);

        // Now merge them
        let _merged_vids = data.merge_equivalent_expressions(vid5, f6, &http, true);

        // vid6 should now resolve to vid5 (or vice versa)
        let resolved_vid6 = data.resolve_vid(vid6);
        let resolved_vid5 = data.resolve_vid(vid5);
        assert_eq!(resolved_vid5, resolved_vid6);
    }

    #[test]
    fn test_propagate_divisibility_transitive() {
        let mut data = FactorData::default();
        let mut http = MockFactorDbClient::new();
        http.expect_cached_factors().return_const(None);

        let (a, _) = add_factor_node(&mut data, Factor::from("a"), None, &http);
        let (b, _) = add_factor_node(&mut data, Factor::from("b"), None, &http);
        let (c, _) = add_factor_node(&mut data, Factor::from("c"), None, &http);

        // a divides b
        data.propagate_divisibility(a, b, false);
        // b divides c
        data.propagate_divisibility(b, c, false);

        // Should know a divides c transitively
        assert!(data.is_known_factor(a, c));

        // And direct ones
        assert!(data.is_known_factor(a, b));
        assert!(data.is_known_factor(b, c));
    }

    #[test]
    fn test_rule_out_divisibility_propagation() {
        let mut data = FactorData::default();
        let mut http = MockFactorDbClient::new();
        http.expect_cached_factors().return_const(None);

        let (a, _) = add_factor_node(&mut data, Factor::from("a"), None, &http);
        let (b, _) = add_factor_node(&mut data, Factor::from("b"), None, &http);
        let (c, _) = add_factor_node(&mut data, Factor::from("c"), None, &http);

        // c divides b (c is a factor of b)
        data.propagate_divisibility(c, b, false);

        // Rule out a divides b (a is NOT a factor of b)
        data.rule_out_divisibility(a, b);

        // If A !| B. And C | B. Does A !| C? Not necessarily. 2 !| 9, 3 | 9. 2 !| 3.
        // But if A | C and C | B, then A | B.
        // So if A !| B, and C | B, then A cannot divide C?
        // If A | C, then since C | B -> A | B. But A !| B. Contradiction.
        // So yes, A !| C.

        use crate::graph::Divisibility::NotFactor;
        assert_eq!(data.get_edge(a, c), Some(NotFactor));
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 1)]
    pub async fn test_huge_u_memory_usage() {
        const ID: EntryId = 1100000005875321487;
        const EXPR: &str = "(10^200000-1)/9-10^58838";

        const LISTED_ALGEBRAIC_FACTORS_URL: &str =
            formatcp!("https://factordb.com/frame_moreinfo.php?id={ID}");

        #[allow(non_local_definitions)]
        impl FactorDbClientReadIdsAndExprs for MockFactorDbClient {
            fn read_ids_and_exprs<'a>(
                &self,
                _haystack: &'a str,
            ) -> impl Iterator<Item = (EntryId, &'a str)> {
                once((ID, &*String::from(EXPR).leak()))
            }
        }

        simple_log::console("info").unwrap();
        let mut http = MockFactorDbClient::new();
        let mut sys = sysinfo::System::new_with_specifics(
            RefreshKind::nothing().with_memory(MemoryRefreshKind::everything()),
        );

        http.expect_known_factors_as_digits()
            .returning(|_, _, _| ProcessedStatusApiResponse {
                status: Some(Unknown),
                factors: Box::new([Factor::from(
                    &*repeat('1')
                        .take(141_161)
                        .chain(once('0'))
                        .chain(repeat('1').take(58838))
                        .collect::<String>(),
                )]),
                id: Some(ID),
            });
        http.expect_cached_factors().return_const(None);
        http.expect_try_get_and_decode()
            .with(eq(&*LISTED_ALGEBRAIC_FACTORS_URL))
            .returning(|_| Some(HipStr::from_static("")));
        http.expect_try_get_expression_form()
            .returning(|_| Some(Factor::from(EXPR)));
        http.expect_try_report_factor()
            .return_const(ReportFactorResult::DoesNotDivide);

        FAILED_U_SUBMISSIONS_OUT
            .get_or_init(async || {
                Mutex::new(File::create_new(temp_dir().join(rng().next_u64().to_string())).unwrap())
            })
            .await;

        // ensure expr uses heap space
        let expr = Factor::from(EXPR);
        let mut reg = stats_alloc::Region::new(&GLOBAL);
        black_box(find_and_submit_factors(&http, ID, expr, false).await);

        log_stats(&mut reg, &mut sys, &mut None);
    }

    #[test]
    fn test_recursive_add_factor_node_with_merge() {
        use crate::NumberSpecifier::{Expression, Id};
        use crate::net::MockFactorDbClient;
        use crate::net::NumberStatus::PartlyFactoredComposite;
        use crate::net::ProcessedStatusApiResponse;

        let mut data = FactorData::default();
        let mut http = MockFactorDbClient::new();

        let fa = Factor::from("A");
        let fb = Factor::from("B");

        // Expectations for cached_factors(Id(1))
        // Called for "A" initially, and then for "B" during recursion.
        http.expect_cached_factors()
            .withf(|id| matches!(id, Id(1)))
            .times(2)
            .returning({
                let fb = fb.clone();
                move |_| {
                    Some(ProcessedStatusApiResponse {
                        factors: Box::from([fb.clone()]),
                        status: Some(PartlyFactoredComposite),
                        id: Some(1),
                    })
                }
            });

        // Expectation for cached_factors(Expression("B"))
        // Called to get entry_id for subfactor "B"
        http.expect_cached_factors()
            .withf({
                let fb = fb.clone();
                move |id| {
                    if let Expression(cow) = id {
                        **cow == fb
                    } else {
                        false
                    }
                }
            })
            .returning(|_| {
                Some(ProcessedStatusApiResponse {
                    factors: Box::from([]),
                    status: Some(PartlyFactoredComposite),
                    id: Some(1),
                })
            });

        // This should not panic
        let (vid, added) = add_factor_node(&mut data, fa.clone(), Some(1), &http);
        assert!(added);
        assert_eq!(data.get_factor(vid), fa);
    }
}
