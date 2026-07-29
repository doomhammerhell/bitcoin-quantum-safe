//! Rust-side PO-6 structural invariant refinement witnesses.
//!
//! This executable mirrors the Coq extraction harness for UTXO-domain
//! preservation. It reports the explicit fresh-id/domain-bound precondition used
//! by the Coq theorem and only observes final-state invariants when that
//! precondition holds. Boundary cases that would require a txid freshness /
//! collision-resistance argument are included but marked as outside the theorem
//! premise.

use std::collections::HashMap;

use pq_witness_protocol::compute_txid;
use pq_witness_protocol::params::MigrationConfig;
use pq_witness_protocol::types::{
    Block, OutPoint, Output, Transaction, TxInput, TxOutput, UtxoSet,
};
use pq_witness_protocol::{valid_block_structural, validate_and_apply_block_structural};
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

fn case_json(index: usize, case: &BlockCase) -> Value {
    let (utxo, projection, block) = build_block_case(case);
    let output_count = block_output_count(case);
    let next_fresh_id = case.fresh_id + output_count;
    let pre_domain = pre_domain_ids(case);
    let pre_domain_unique = !has_duplicate_ids(&pre_domain);
    let pre_domain_below_fresh = pre_domain.iter().all(|id| *id < case.fresh_id);
    let freshness_precondition = pre_domain_unique && pre_domain_below_fresh;
    let valid_block = valid_block_structural(&utxo, &block, case.height, &config());
    let final_state = validate_and_apply_block_structural(&utxo, &block, case.height, &config());
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

    let theorem_applicable = freshness_precondition && final_state.is_some();
    let theorem_conclusion_holds = if theorem_applicable {
        Some(final_domain_unique == Some(true) && final_domain_below_next_fresh == Some(true))
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
        },
        "theorem": {
            "name": "apply_valid_block_structural_preserves_domain_nodup",
            "applicable": theorem_applicable,
            "conclusion_holds": theorem_conclusion_holds,
            "non_applicability_reason": boundary_reason(freshness_precondition, final_state.as_ref()),
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
        "model": "utxo-domain-invariant-refinement",
        "evidence": "per-case-structured-invariant-witnesses",
        "proof_boundary": "Coq theorem apply_valid_block_structural_preserves_domain_nodup under explicit fresh-id/domain-bound precondition",
        "case_count": cases.len(),
        "cases": case_values,
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&output).expect("JSON serialization should succeed")
    );
}
