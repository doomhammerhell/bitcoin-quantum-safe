//! Rust-side PO-6 structural invariant refinement witnesses.
//!
//! This executable mirrors the Coq extraction harness for UTXO-domain
//! preservation, total-value non-increase, migration monotonicity, and freeze
//! observables. It reports the explicit fresh-id/domain-bound precondition used
//! by the domain theorem and marks cases that would require a txid freshness /
//! collision-resistance argument as outside that theorem premise.

use std::collections::HashMap;

use pq_witness_protocol::compute_txid;
use pq_witness_protocol::params::MigrationConfig;
use pq_witness_protocol::types::{
    Block, OutPoint, Output, Transaction, TxInput, TxOutput, UtxoSet,
};
use pq_witness_protocol::{
    delta_tx, valid_block_structural, valid_tx_structural, validate_and_apply_block_structural,
};
use serde_json::{json, Value};

type AbstractId = u64;
type OutpointProjection = HashMap<AbstractId, OutPoint>;

#[derive(Clone, Copy)]
struct OutputShape {
    script_version: u8,
    value: u64,
}

impl OutputShape {
    const fn new(script_version: u8, value: u64) -> Self {
        Self {
            script_version,
            value,
        }
    }
}

struct BlockTxSpec {
    inputs: Vec<AbstractId>,
    outputs: Vec<OutputShape>,
}

struct BlockCase {
    name: &'static str,
    height: u64,
    utxo: Vec<(AbstractId, OutputShape)>,
    txs: Vec<BlockTxSpec>,
    fresh_id: AbstractId,
    observed_ids: Vec<AbstractId>,
}

fn config() -> MigrationConfig {
    MigrationConfig {
        announcement_height: 100,
        cutover_height: 160,
    }
}

fn commitment(seed: u8) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = seed
            .wrapping_add((i as u8).wrapping_mul(31))
            .wrapping_add((i / 7) as u8);
    }
    out
}

fn initial_outpoint(id: AbstractId) -> OutPoint {
    let mut txid = [0u8; 32];
    txid[..8].copy_from_slice(&id.to_le_bytes());
    txid[31] = 0xA5;
    OutPoint { txid, vout: 0 }
}

fn output_from_shape(shape: OutputShape, seed: u8) -> Output {
    Output {
        script_version: shape.script_version,
        commitment: commitment(seed),
        value: shape.value,
    }
}

fn tx_output_from_shape(shape: OutputShape, seed: u8) -> TxOutput {
    TxOutput {
        script_version: shape.script_version,
        commitment: commitment(seed),
        value: shape.value,
    }
}

fn input_from_outpoint(outpoint: OutPoint) -> TxInput {
    TxInput {
        outpoint,
        witness: vec![0xDE, 0xAD],
    }
}

fn build_initial_utxo(entries: &[(AbstractId, OutputShape)]) -> (UtxoSet, OutpointProjection) {
    let mut utxo = UtxoSet::new();
    let mut projection = OutpointProjection::new();

    for (index, (id, shape)) in entries.iter().enumerate() {
        let outpoint = initial_outpoint(*id);
        projection.insert(*id, outpoint.clone());
        utxo.insert(outpoint, output_from_shape(*shape, 0x40 + index as u8));
    }

    (utxo, projection)
}

fn ensure_initial_projection(projection: &mut OutpointProjection, id: AbstractId) {
    projection.entry(id).or_insert_with(|| initial_outpoint(id));
}

fn register_fresh_outputs(
    projection: &mut OutpointProjection,
    fresh_id: AbstractId,
    tx: &Transaction,
) {
    let txid = compute_txid(tx);
    for index in 0..tx.outputs.len() {
        projection.insert(
            fresh_id + index as u64,
            OutPoint {
                txid,
                vout: index as u32,
            },
        );
    }
}

fn build_transaction(
    projection: &mut OutpointProjection,
    input_ids: &[AbstractId],
    output_shapes: &[OutputShape],
    output_seed_base: u8,
) -> Transaction {
    let inputs = input_ids
        .iter()
        .map(|id| {
            ensure_initial_projection(projection, *id);
            input_from_outpoint(projection[id].clone())
        })
        .collect();
    let outputs = output_shapes
        .iter()
        .enumerate()
        .map(|(index, shape)| tx_output_from_shape(*shape, output_seed_base + index as u8))
        .collect();

    Transaction {
        version: 2,
        inputs,
        outputs,
        locktime: 0,
    }
}

fn block_cases() -> Vec<BlockCase> {
    vec![
        BlockCase {
            name: "empty-block",
            height: 50,
            utxo: vec![],
            txs: vec![],
            fresh_id: 300,
            observed_ids: vec![],
        },
        BlockCase {
            name: "single-valid-block",
            height: 50,
            utxo: vec![(20, OutputShape::new(0, 50))],
            txs: vec![BlockTxSpec {
                inputs: vec![20],
                outputs: vec![OutputShape::new(2, 50)],
            }],
            fresh_id: 310,
            observed_ids: vec![20, 310],
        },
        BlockCase {
            name: "structural-pq-spend-block-boundary",
            height: 50,
            utxo: vec![(23, OutputShape::new(2, 50))],
            txs: vec![BlockTxSpec {
                inputs: vec![23],
                outputs: vec![OutputShape::new(2, 50)],
            }],
            fresh_id: 350,
            observed_ids: vec![23, 350],
        },
        BlockCase {
            name: "grace-period-migrates-legacy-to-pq",
            height: 120,
            utxo: vec![(30, OutputShape::new(0, 100))],
            txs: vec![BlockTxSpec {
                inputs: vec![30],
                outputs: vec![OutputShape::new(2, 90)],
            }],
            fresh_id: 360,
            observed_ids: vec![30, 360],
        },
        BlockCase {
            name: "grace-period-rejects-legacy-recreation",
            height: 120,
            utxo: vec![(31, OutputShape::new(0, 100))],
            txs: vec![BlockTxSpec {
                inputs: vec![31],
                outputs: vec![OutputShape::new(0, 90)],
            }],
            fresh_id: 370,
            observed_ids: vec![31, 370],
        },
        BlockCase {
            name: "post-cutover-preserves-frozen-legacy-with-pq-spend",
            height: 180,
            utxo: vec![(40, OutputShape::new(0, 70)), (41, OutputShape::new(2, 50))],
            txs: vec![BlockTxSpec {
                inputs: vec![41],
                outputs: vec![OutputShape::new(2, 45)],
            }],
            fresh_id: 380,
            observed_ids: vec![40, 41, 380],
        },
        BlockCase {
            name: "post-cutover-rejects-frozen-legacy-spend",
            height: 180,
            utxo: vec![(42, OutputShape::new(0, 70))],
            txs: vec![BlockTxSpec {
                inputs: vec![42],
                outputs: vec![OutputShape::new(2, 70)],
            }],
            fresh_id: 390,
            observed_ids: vec![42, 390],
        },
        BlockCase {
            name: "post-cutover-mixed-inputs-rejected",
            height: 180,
            utxo: vec![(43, OutputShape::new(0, 40)), (44, OutputShape::new(2, 40))],
            txs: vec![BlockTxSpec {
                inputs: vec![43, 44],
                outputs: vec![OutputShape::new(2, 70)],
            }],
            fresh_id: 400,
            observed_ids: vec![43, 44, 400],
        },
        BlockCase {
            name: "invalid-missing-input-block",
            height: 50,
            utxo: vec![],
            txs: vec![BlockTxSpec {
                inputs: vec![299],
                outputs: vec![OutputShape::new(2, 1)],
            }],
            fresh_id: 320,
            observed_ids: vec![299, 320],
        },
        BlockCase {
            name: "sequential-intrablock-legacy-dependency",
            height: 50,
            utxo: vec![(21, OutputShape::new(0, 100))],
            txs: vec![
                BlockTxSpec {
                    inputs: vec![21],
                    outputs: vec![OutputShape::new(0, 100)],
                },
                BlockTxSpec {
                    inputs: vec![330],
                    outputs: vec![OutputShape::new(2, 90)],
                },
            ],
            fresh_id: 330,
            observed_ids: vec![21, 330, 331],
        },
        BlockCase {
            name: "intrablock-double-spend-rejected",
            height: 50,
            utxo: vec![(22, OutputShape::new(0, 100))],
            txs: vec![
                BlockTxSpec {
                    inputs: vec![22],
                    outputs: vec![OutputShape::new(2, 50)],
                },
                BlockTxSpec {
                    inputs: vec![22],
                    outputs: vec![OutputShape::new(2, 50)],
                },
            ],
            fresh_id: 340,
            observed_ids: vec![22, 340, 341],
        },
        BlockCase {
            name: "fresh-bound-precondition-fails",
            height: 50,
            utxo: vec![(20, OutputShape::new(0, 50)), (400, OutputShape::new(2, 7))],
            txs: vec![BlockTxSpec {
                inputs: vec![20],
                outputs: vec![OutputShape::new(2, 40)],
            }],
            fresh_id: 390,
            observed_ids: vec![20, 390, 400],
        },
        BlockCase {
            name: "fresh-id-collision-boundary",
            height: 50,
            utxo: vec![(20, OutputShape::new(0, 50)), (390, OutputShape::new(2, 7))],
            txs: vec![BlockTxSpec {
                inputs: vec![20],
                outputs: vec![OutputShape::new(2, 40)],
            }],
            fresh_id: 390,
            observed_ids: vec![20],
        },
    ]
}

fn build_block_case(case: &BlockCase) -> (UtxoSet, OutpointProjection, Block) {
    let (utxo, mut projection) = build_initial_utxo(&case.utxo);
    let mut block = Vec::with_capacity(case.txs.len());
    let mut next_fresh_id = case.fresh_id;

    for (tx_index, spec) in case.txs.iter().enumerate() {
        let tx = build_transaction(
            &mut projection,
            &spec.inputs,
            &spec.outputs,
            0x60 + tx_index as u8,
        );
        register_fresh_outputs(&mut projection, next_fresh_id, &tx);
        next_fresh_id += tx.outputs.len() as u64;
        block.push(tx);
    }

    for id in &case.observed_ids {
        ensure_initial_projection(&mut projection, *id);
    }

    (utxo, projection, block)
}

fn has_duplicate_ids(ids: &[AbstractId]) -> bool {
    for i in 0..ids.len() {
        for j in (i + 1)..ids.len() {
            if ids[i] == ids[j] {
                return true;
            }
        }
    }
    false
}

fn block_output_count(case: &BlockCase) -> u64 {
    case.txs.iter().map(|tx| tx.outputs.len() as u64).sum()
}

fn block_input_ids(case: &BlockCase) -> Vec<AbstractId> {
    case.txs
        .iter()
        .flat_map(|tx| tx.inputs.iter().copied())
        .collect()
}

fn pre_domain_ids(case: &BlockCase) -> Vec<AbstractId> {
    case.utxo.iter().map(|(id, _)| *id).collect()
}

fn utxo_total_value(utxo: &UtxoSet) -> u64 {
    utxo.values().map(|output| output.value).sum()
}

fn is_pq_script_version(script_version: u8) -> bool {
    script_version == 2
}

fn legacy_utxo_count(utxo: &UtxoSet) -> u64 {
    utxo.values()
        .filter(|output| !is_pq_script_version(output.script_version))
        .count() as u64
}

fn frozen_utxo_count(height: u64, config: &MigrationConfig, utxo: &UtxoSet) -> u64 {
    if height < config.cutover_height {
        0
    } else {
        legacy_utxo_count(utxo)
    }
}

fn all_present_inputs_pq_or_missing(utxo: &UtxoSet, tx: &Transaction) -> bool {
    tx.inputs
        .iter()
        .all(|input| match utxo.get(&input.outpoint) {
            Some(spent) => is_pq_script_version(spent.script_version),
            None => true,
        })
}

fn accepted_block_inputs_pq_or_missing(
    utxo: &UtxoSet,
    block: &Block,
    height: u64,
    config: &MigrationConfig,
) -> bool {
    let mut local_utxo = utxo.clone();

    for tx in block {
        if valid_tx_structural(&local_utxo, tx, height, config) {
            if !all_present_inputs_pq_or_missing(&local_utxo, tx) {
                return false;
            }
            delta_tx(&mut local_utxo, tx);
        } else {
            return true;
        }
    }

    true
}

fn present_abstract_ids(
    observed_ids: &[AbstractId],
    projection: &OutpointProjection,
    utxo: &UtxoSet,
) -> Vec<AbstractId> {
    observed_ids
        .iter()
        .copied()
        .filter(|id| {
            projection
                .get(id)
                .map(|outpoint| utxo.contains_key(outpoint))
                .unwrap_or(false)
        })
        .collect()
}

fn observed_output(output: Option<&Output>) -> Value {
    match output {
        None => Value::Null,
        Some(output) => json!({
            "script_version": output.script_version,
            "value": output.value,
        }),
    }
}

fn observed_state(
    observed_ids: &[AbstractId],
    projection: &OutpointProjection,
    utxo: &UtxoSet,
) -> Value {
    let entries: Vec<Value> = observed_ids
        .iter()
        .map(|id| {
            let output = projection.get(id).and_then(|outpoint| utxo.get(outpoint));
            json!({
                "id": id,
                "present": output.is_some(),
                "output": observed_output(output),
            })
        })
        .collect();
    Value::Array(entries)
}

fn transaction_json(tx: &Transaction, projection: &OutpointProjection) -> Value {
    let inputs: Vec<Value> = tx
        .inputs
        .iter()
        .map(|input| {
            projection
                .iter()
                .find_map(|(id, outpoint)| {
                    if outpoint == &input.outpoint {
                        Some(json!(id))
                    } else {
                        None
                    }
                })
                .unwrap_or(Value::Null)
        })
        .collect();
    let outputs: Vec<Value> = tx
        .outputs
        .iter()
        .map(|output| {
            json!({
                "script_version": output.script_version,
                "value": output.value,
            })
        })
        .collect();

    json!({
        "inputs": inputs,
        "outputs": outputs,
    })
}

fn block_json(block: &Block, projection: &OutpointProjection) -> Value {
    let transactions: Vec<Value> = block
        .iter()
        .map(|tx| transaction_json(tx, projection))
        .collect();
    json!({ "transactions": transactions })
}

fn boundary_reason(freshness_precondition: bool, final_state: Option<&UtxoSet>) -> Value {
    if !freshness_precondition {
        json!("fresh-id precondition false; txid/freshness collision boundary outside theorem")
    } else if final_state.is_none() {
        json!("block rejected; final-state preservation theorem premise not satisfied")
    } else {
        Value::Null
    }
}

fn migration_reason(post_announcement: bool, final_state: Option<&UtxoSet>) -> Value {
    if !post_announcement {
        json!("pre-announcement; migration monotonicity theorem premise not active")
    } else if final_state.is_none() {
        json!("block rejected; migration monotonicity theorem premise not satisfied")
    } else {
        Value::Null
    }
}

fn cutover_reason(post_cutover: bool, final_state: Option<&UtxoSet>) -> Value {
    if !post_cutover {
        json!("pre-cutover; freeze theorem premise not active")
    } else if final_state.is_none() {
        json!("block rejected; freeze theorem premise not satisfied")
    } else {
        Value::Null
    }
}

fn frozen_count_reason(
    config_order: bool,
    post_cutover: bool,
    final_state: Option<&UtxoSet>,
) -> Value {
    if !config_order {
        json!("invalid migration config ordering; frozen-count theorem premise not satisfied")
    } else {
        cutover_reason(post_cutover, final_state)
    }
}

fn case_json(index: usize, case: &BlockCase) -> Value {
    let (utxo, projection, block) = build_block_case(case);
    let migration_config = config();
    let output_count = block_output_count(case);
    let next_fresh_id = case.fresh_id + output_count;
    let pre_domain = pre_domain_ids(case);
    let pre_total_value = utxo_total_value(&utxo);
    let pre_legacy_count = legacy_utxo_count(&utxo);
    let pre_frozen_count = frozen_utxo_count(case.height, &migration_config, &utxo);
    let pre_domain_unique = !has_duplicate_ids(&pre_domain);
    let pre_domain_below_fresh = pre_domain.iter().all(|id| *id < case.fresh_id);
    let freshness_precondition = pre_domain_unique && pre_domain_below_fresh;
    let post_announcement = migration_config.announcement_height <= case.height;
    let post_cutover = migration_config.cutover_height <= case.height;
    let config_order = migration_config.announcement_height <= migration_config.cutover_height;
    let valid_block = valid_block_structural(&utxo, &block, case.height, &migration_config);
    let final_state =
        validate_and_apply_block_structural(&utxo, &block, case.height, &migration_config);
    let observed_final = final_state.as_ref().filter(|_| freshness_precondition);

    let final_present_ids = observed_final
        .map(|final_utxo| present_abstract_ids(&case.observed_ids, &projection, final_utxo));
    let final_domain_unique = final_present_ids
        .as_ref()
        .map(|ids| !has_duplicate_ids(ids));
    let final_domain_below_next_fresh = final_present_ids
        .as_ref()
        .map(|ids| ids.iter().all(|id| *id < next_fresh_id));
    let spent_inputs = block_input_ids(case);
    let spent_inputs_absent = observed_final.map(|final_utxo| {
        spent_inputs.iter().all(|id| {
            projection
                .get(id)
                .map(|outpoint| !final_utxo.contains_key(outpoint))
                .unwrap_or(true)
        })
    });
    let final_total_value = observed_final.map(utxo_total_value);
    let final_total_value_lte_pre =
        final_total_value.map(|total_value| total_value <= pre_total_value);
    let final_legacy_count = final_state.as_ref().map(legacy_utxo_count);
    let final_legacy_count_lte_pre_after_announcement = if post_announcement {
        final_legacy_count.map(|count| count <= pre_legacy_count)
    } else {
        None
    };
    let final_frozen_count = final_state
        .as_ref()
        .map(|final_utxo| frozen_utxo_count(case.height, &migration_config, final_utxo));
    let final_frozen_count_lte_pre_after_cutover = if config_order && post_cutover {
        final_frozen_count.map(|count| count <= pre_frozen_count)
    } else {
        None
    };
    let accepted_inputs_pq_or_missing =
        accepted_block_inputs_pq_or_missing(&utxo, &block, case.height, &migration_config);
    let accepted_inputs_pq_or_missing_after_cutover = if post_cutover {
        Some(accepted_inputs_pq_or_missing)
    } else {
        None
    };

    let theorem_applicable = freshness_precondition && final_state.is_some();
    let theorem_conclusion_holds = if theorem_applicable {
        Some(final_domain_unique == Some(true) && final_domain_below_next_fresh == Some(true))
    } else {
        None
    };
    let value_theorem_conclusion_holds = if theorem_applicable {
        Some(final_total_value_lte_pre == Some(true))
    } else {
        None
    };
    let migration_theorem_applicable = post_announcement && final_state.is_some();
    let migration_theorem_conclusion_holds = if migration_theorem_applicable {
        Some(final_legacy_count_lte_pre_after_announcement == Some(true))
    } else {
        None
    };
    let freeze_theorem_applicable = post_cutover && final_state.is_some();
    let freeze_theorem_conclusion_holds = if freeze_theorem_applicable {
        Some(accepted_inputs_pq_or_missing)
    } else {
        None
    };
    let frozen_count_theorem_applicable = config_order && post_cutover && final_state.is_some();
    let frozen_count_theorem_conclusion_holds = if frozen_count_theorem_applicable {
        Some(final_frozen_count_lte_pre_after_cutover == Some(true))
    } else {
        None
    };

    json!({
        "kind": "block-invariant",
        "index": index,
        "name": case.name,
        "height": case.height,
        "fresh_id": case.fresh_id,
        "next_fresh_id": next_fresh_id,
        "observed_ids": case.observed_ids,
        "pre_domain": pre_domain,
        "pre_total_value": pre_total_value,
        "pre_legacy_count": pre_legacy_count,
        "pre_frozen_count": pre_frozen_count,
        "pre_state": observed_state(&case.observed_ids, &projection, &utxo),
        "block": block_json(&block, &projection),
        "spent_input_ids": spent_inputs,
        "preconditions": {
            "pre_domain_unique": pre_domain_unique,
            "pre_domain_below_fresh": pre_domain_below_fresh,
            "fresh_id_assumption_holds": freshness_precondition,
        },
        "result": {
            "valid_block": valid_block,
            "final_state": observed_final
                .map(|final_utxo| observed_state(&case.observed_ids, &projection, final_utxo))
                .unwrap_or(Value::Null),
            "final_domain_unique": final_domain_unique,
            "final_domain_below_next_fresh": final_domain_below_next_fresh,
            "spent_inputs_absent": spent_inputs_absent,
            "final_total_value": final_total_value,
            "final_total_value_lte_pre": final_total_value_lte_pre,
            "final_legacy_count": final_legacy_count,
            "final_legacy_count_lte_pre_after_announcement": final_legacy_count_lte_pre_after_announcement,
            "final_frozen_count": final_frozen_count,
            "final_frozen_count_lte_pre_after_cutover": final_frozen_count_lte_pre_after_cutover,
            "accepted_inputs_pq_or_missing": accepted_inputs_pq_or_missing,
            "accepted_inputs_pq_or_missing_after_cutover": accepted_inputs_pq_or_missing_after_cutover,
        },
        "theorem": {
            "name": "apply_valid_block_structural_preserves_domain_nodup",
            "applicable": theorem_applicable,
            "conclusion_holds": theorem_conclusion_holds,
            "non_applicability_reason": boundary_reason(freshness_precondition, final_state.as_ref()),
        },
        "value_theorem": {
            "name": "apply_valid_block_structural_preserves_total_value",
            "applicable": theorem_applicable,
            "conclusion_holds": value_theorem_conclusion_holds,
            "non_applicability_reason": boundary_reason(freshness_precondition, final_state.as_ref()),
        },
        "migration_theorem": {
            "name": "apply_valid_block_structural_legacy_count_nonincreasing_after_announcement",
            "applicable": migration_theorem_applicable,
            "conclusion_holds": migration_theorem_conclusion_holds,
            "non_applicability_reason": migration_reason(post_announcement, final_state.as_ref()),
        },
        "freeze_theorem": {
            "name": "apply_valid_block_structural_inputs_pq_after_cutover",
            "applicable": freeze_theorem_applicable,
            "conclusion_holds": freeze_theorem_conclusion_holds,
            "non_applicability_reason": cutover_reason(post_cutover, final_state.as_ref()),
        },
        "frozen_count_theorem": {
            "name": "apply_valid_block_structural_frozen_count_nonincreasing_after_cutover",
            "applicable": frozen_count_theorem_applicable,
            "conclusion_holds": frozen_count_theorem_conclusion_holds,
            "non_applicability_reason": frozen_count_reason(config_order, post_cutover, final_state.as_ref()),
        },
    })
}

fn main() {
    let cases = block_cases();
    let case_values: Vec<Value> = cases
        .iter()
        .enumerate()
        .map(|(index, case)| case_json(index, case))
        .collect();
    let output = json!({
        "model": "utxo-domain-value-migration-freeze-invariant-refinement",
        "evidence": "per-case-structured-invariant-witnesses",
        "proof_boundary": "Coq theorems for domain preservation, value non-increase, legacy-output non-increase after announcement, PQ-only accepted inputs after cutover, and frozen-count non-increase after cutover under their explicit premises",
        "case_count": cases.len(),
        "cases": case_values,
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&output).expect("JSON serialization should succeed")
    );
}
