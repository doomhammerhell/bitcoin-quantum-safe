//! Rust-side PO-5 transition-kernel adapter refinement witnesses.
//!
//! This executable observes the deployed `TransitionKernel` adapter boundary:
//! `StructuralTxReport` and `StructuralBlockReport`. It is compared against a
//! Coq-extracted oracle adapter built from the structural UTXO transition
//! model. The comparison emits per-case structured witnesses over the same
//! abstract-outpoint projection as the transition refinement matrix and does
//! not claim compiler, SHA-256,
//! cryptographic witness, or store-backend correctness.

use std::collections::HashMap;

use pq_witness_protocol::compute_txid;
use pq_witness_protocol::params::MigrationConfig;
use pq_witness_protocol::transition_core::{
    DeployedTransitionKernel, StructuralBlockReport, StructuralTxReport, TransitionKernel,
};
use pq_witness_protocol::types::{
    Block, OutPoint, Output, Transaction, TxInput, TxOutput, UtxoSet,
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

struct TxCase {
    name: &'static str,
    height: u64,
    utxo: Vec<(AbstractId, OutputShape)>,
    inputs: Vec<AbstractId>,
    outputs: Vec<OutputShape>,
    fresh_id: AbstractId,
    observed_ids: Vec<AbstractId>,
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

fn tx_cases() -> Vec<TxCase> {
    vec![
        TxCase {
            name: "empty-transaction",
            height: 50,
            utxo: vec![],
            inputs: vec![],
            outputs: vec![],
            fresh_id: 100,
            observed_ids: vec![],
        },
        TxCase {
            name: "valid-preactivation-legacy-to-legacy",
            height: 99,
            utxo: vec![
                (1, OutputShape::new(0, 50_000)),
                (9, OutputShape::new(2, 7_000)),
            ],
            inputs: vec![1],
            outputs: vec![OutputShape::new(0, 40_000)],
            fresh_id: 100,
            observed_ids: vec![1, 9, 100],
        },
        TxCase {
            name: "valid-grace-legacy-to-pq",
            height: 120,
            utxo: vec![(2, OutputShape::new(0, 50_000))],
            inputs: vec![2],
            outputs: vec![OutputShape::new(2, 50_000)],
            fresh_id: 110,
            observed_ids: vec![2, 110],
        },
        TxCase {
            name: "structural-pq-spend-boundary",
            height: 50,
            utxo: vec![(13, OutputShape::new(2, 50_000))],
            inputs: vec![13],
            outputs: vec![OutputShape::new(2, 50_000)],
            fresh_id: 210,
            observed_ids: vec![13, 210],
        },
        TxCase {
            name: "missing-input",
            height: 50,
            utxo: vec![],
            inputs: vec![99],
            outputs: vec![OutputShape::new(2, 1)],
            fresh_id: 120,
            observed_ids: vec![99, 120],
        },
        TxCase {
            name: "duplicate-input",
            height: 50,
            utxo: vec![(3, OutputShape::new(0, 100))],
            inputs: vec![3, 3],
            outputs: vec![OutputShape::new(2, 50)],
            fresh_id: 130,
            observed_ids: vec![3, 130],
        },
        TxCase {
            name: "value-inflation",
            height: 50,
            utxo: vec![(4, OutputShape::new(0, 50))],
            inputs: vec![4],
            outputs: vec![OutputShape::new(2, 100)],
            fresh_id: 140,
            observed_ids: vec![4, 140],
        },
        TxCase {
            name: "legacy-output-after-ha",
            height: 100,
            utxo: vec![(5, OutputShape::new(0, 100))],
            inputs: vec![5],
            outputs: vec![OutputShape::new(0, 100)],
            fresh_id: 150,
            observed_ids: vec![5, 150],
        },
        TxCase {
            name: "frozen-legacy-spend-at-cutover",
            height: 160,
            utxo: vec![(6, OutputShape::new(0, 100))],
            inputs: vec![6],
            outputs: vec![OutputShape::new(2, 100)],
            fresh_id: 160,
            observed_ids: vec![6, 160],
        },
        TxCase {
            name: "post-cutover-taproot-rejection",
            height: 160,
            utxo: vec![(7, OutputShape::new(1, 100))],
            inputs: vec![7],
            outputs: vec![OutputShape::new(2, 100)],
            fresh_id: 170,
            observed_ids: vec![7, 170],
        },
        TxCase {
            name: "mixed-inputs-post-cutover",
            height: 160,
            utxo: vec![(8, OutputShape::new(2, 60)), (9, OutputShape::new(0, 40))],
            inputs: vec![8, 9],
            outputs: vec![OutputShape::new(2, 100)],
            fresh_id: 180,
            observed_ids: vec![8, 9, 180],
        },
        TxCase {
            name: "multi-input-fee-conservation",
            height: 120,
            utxo: vec![(10, OutputShape::new(0, 70)), (11, OutputShape::new(0, 50))],
            inputs: vec![10, 11],
            outputs: vec![OutputShape::new(2, 100), OutputShape::new(2, 10)],
            fresh_id: 190,
            observed_ids: vec![10, 11, 190, 191],
        },
        TxCase {
            name: "script-version-255-frozen",
            height: 160,
            utxo: vec![(12, OutputShape::new(255, 100))],
            inputs: vec![12],
            outputs: vec![OutputShape::new(2, 100)],
            fresh_id: 200,
            observed_ids: vec![12, 200],
        },
    ]
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

fn final_state(
    observed_ids: &[AbstractId],
    projection: &OutpointProjection,
    utxo: Option<&UtxoSet>,
) -> Value {
    match utxo {
        None => Value::Null,
        Some(utxo) => observed_state(observed_ids, projection, utxo),
    }
}

fn transaction_witness(inputs: &[AbstractId], outputs: &[OutputShape]) -> Value {
    let outputs: Vec<Value> = outputs
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

fn tx_report_witness(report: &StructuralTxReport) -> Value {
    json!({
        "has_duplicate_inputs": report.has_duplicate_inputs,
        "all_inputs_present": report.all_inputs_present,
        "input_sum": report.input_sum,
        "output_sum": report.output_sum,
        "migration_ok": report.migration_ok,
        "freeze_ok": report.freeze_ok,
        "valid": report.valid,
    })
}

fn block_report_witness(
    observed_ids: &[AbstractId],
    projection: &OutpointProjection,
    report: &StructuralBlockReport,
) -> Value {
    json!({
        "transitions_ok": report.transitions_ok,
        "cost_ok": report.cost_ok,
        "valid": report.valid,
        "final_utxo": final_state(observed_ids, projection, report.final_utxo.as_ref()),
    })
}

fn tx_case_witness(case_index: usize, case: &TxCase) -> Value {
    let kernel = DeployedTransitionKernel::new();
    let config = config();
    let (utxo, mut projection) = build_initial_utxo(&case.utxo);
    let tx = build_transaction(&mut projection, &case.inputs, &case.outputs, 0x50);
    register_fresh_outputs(&mut projection, case.fresh_id, &tx);
    for id in &case.observed_ids {
        ensure_initial_projection(&mut projection, *id);
    }

    let report = kernel.structural_tx_report(&utxo, &tx, case.height, &config);

    json!({
        "kind": "transaction",
        "index": case_index,
        "name": case.name,
        "height": case.height,
        "fresh_id": case.fresh_id,
        "observed_ids": case.observed_ids,
        "pre_state": observed_state(&case.observed_ids, &projection, &utxo),
        "transaction": transaction_witness(&case.inputs, &case.outputs),
        "report": tx_report_witness(&report),
    })
}

fn block_case_witness(case_index: usize, case: &BlockCase) -> Value {
    let kernel = DeployedTransitionKernel::new();
    let config = config();
    let (utxo, projection, block) = build_block_case(case);

    let report = kernel.structural_block_report(&utxo, &block, case.height, &config);

    let transactions: Vec<Value> = case
        .txs
        .iter()
        .map(|tx| transaction_witness(&tx.inputs, &tx.outputs))
        .collect();

    json!({
        "kind": "block",
        "index": case_index,
        "name": case.name,
        "height": case.height,
        "fresh_id": case.fresh_id,
        "observed_ids": case.observed_ids,
        "pre_state": observed_state(&case.observed_ids, &projection, &utxo),
        "block": {
            "transactions": transactions,
        },
        "report": block_report_witness(&case.observed_ids, &projection, &report),
    })
}

fn main() {
    let tx_cases = tx_cases();
    let block_cases = block_cases();

    let transaction_witnesses: Vec<Value> = tx_cases
        .iter()
        .enumerate()
        .map(|(case_index, case)| tx_case_witness(case_index, case))
        .collect();
    let block_witnesses: Vec<Value> = block_cases
        .iter()
        .enumerate()
        .map(|(case_index, case)| block_case_witness(case_index, case))
        .collect();

    let certificate = json!({
        "model": "transition-kernel-refinement",
        "evidence": "per-case-structured-witnesses",
        "oracle": "CoqExtractedTransitionKernel",
        "rust_adapter": "DeployedTransitionKernel",
        "tx_case_count": tx_cases.len(),
        "block_case_count": block_cases.len(),
        "projection": "coq_nat_outpoint_to_rust_initial_or_fresh_output_id",
        "observed_reports": ["StructuralTxReport", "StructuralBlockReport"],
        "cases": {
            "transactions": transaction_witnesses,
            "blocks": block_witnesses,
        },
    });

    println!("{}", serde_json::to_string_pretty(&certificate).unwrap());
}
