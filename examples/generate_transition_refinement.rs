//! Rust-side PO-5 UTXO transition refinement summary.
//!
//! This executable observes the structural transition boundary shared by the
//! Coq UTXO model and the Rust implementation: duplicate-input rejection,
//! missing-input rejection, value conservation, migration and freeze rules,
//! deterministic `delta_tx`, sequential in-block dependency handling, and the
//! block cost invariant. The comparison uses a canonical projection from
//! abstract Coq outpoint IDs to synthetic Rust `OutPoint`s; it deliberately does
//! not claim SHA-256 txid, UTXO-store backend internals, cryptographic witness
//! validation, or compiler correctness.

use std::collections::{HashMap, HashSet};

use pq_witness_protocol::freeze::check_no_frozen_inputs;
use pq_witness_protocol::migration::check_migration_rules;
use pq_witness_protocol::params::MigrationConfig;
use pq_witness_protocol::types::{
    Block, OutPoint, Output, Transaction, TxInput, TxOutput, UtxoSet,
};
use pq_witness_protocol::weight::{check_block_cost, cost_tx, weight_tx};
use pq_witness_protocol::{
    apply_block_transitions, compute_txid, delta_tx, valid_block, valid_tx,
    validate_and_apply_block,
};

const MODULUS_1: u64 = 1_000_000_007;
const MODULUS_2: u64 = 1_000_000_009;
const MULTIPLIER: u64 = 16_777_619;

type AbstractId = u64;
type OutpointProjection = HashMap<AbstractId, OutPoint>;
type CostShape = (Vec<usize>, usize);

#[derive(Clone, Copy)]
struct Digest {
    h1: u64,
    h2: u64,
}

impl Digest {
    fn new() -> Self {
        Self {
            h1: 2_166_136_261 % MODULUS_1,
            h2: 2_166_136_261 % MODULUS_2,
        }
    }

    fn add_byte(self, byte: u8) -> Self {
        Self {
            h1: ((self.h1 * MULTIPLIER) + u64::from(byte) + 1) % MODULUS_1,
            h2: ((self.h2 * MULTIPLIER) + u64::from(byte) + 1) % MODULUS_2,
        }
    }

    fn add_bool(self, value: bool) -> Self {
        self.add_byte(u8::from(value))
    }

    fn add_u64(mut self, value: u64) -> Self {
        for byte in value.to_le_bytes() {
            self = self.add_byte(byte);
        }
        self
    }

    fn add_string(mut self, value: &str) -> Self {
        self = self.add_u64(value.len() as u64);
        for byte in value.as_bytes() {
            self = self.add_byte(*byte);
        }
        self
    }

    fn add_option_u64(self, value: Option<u64>) -> Self {
        match value {
            None => self.add_bool(false),
            Some(value) => self.add_bool(true).add_u64(value),
        }
    }

    fn add_output(self, output: Option<&Output>) -> Self {
        match output {
            None => self.add_bool(false),
            Some(output) => self
                .add_bool(true)
                .add_u64(u64::from(output.script_version))
                .add_u64(output.value),
        }
    }

    fn add_state(
        mut self,
        observed_ids: &[AbstractId],
        projection: &OutpointProjection,
        utxo: &UtxoSet,
    ) -> Self {
        self = self.add_u64(observed_ids.len() as u64);
        for id in observed_ids {
            self = self.add_u64(*id);
            let output = projection.get(id).and_then(|outpoint| utxo.get(outpoint));
            self = self.add_output(output);
        }
        self
    }
}

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

struct CostCase {
    name: &'static str,
    shapes: Vec<CostShape>,
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

fn cost_cases() -> Vec<CostCase> {
    vec![
        CostCase {
            name: "empty-cost-block",
            shapes: vec![],
        },
        CostCase {
            name: "single-small-cost",
            shapes: vec![(vec![0], 1)],
        },
        CostCase {
            name: "multi-witness-cost",
            shapes: vec![(vec![3, 5], 2), (vec![], 0)],
        },
        CostCase {
            name: "exact-cost-limit",
            shapes: vec![(vec![3_999_816], 0)],
        },
        CostCase {
            name: "over-cost-limit",
            shapes: vec![(vec![4_000_000], 0)],
        },
    ]
}

fn has_duplicate_inputs(tx: &Transaction) -> bool {
    let mut seen = HashSet::with_capacity(tx.inputs.len());
    tx.inputs.iter().any(|input| !seen.insert(&input.outpoint))
}

fn sum_input_values(utxo: &UtxoSet, tx: &Transaction) -> Option<u64> {
    let mut total = 0u64;
    for input in &tx.inputs {
        let output = utxo.get(&input.outpoint)?;
        total += output.value;
    }
    Some(total)
}

fn sum_output_values(tx: &Transaction) -> u64 {
    tx.outputs.iter().map(|output| output.value).sum()
}

fn structural_tx_cost(tx: &Transaction) -> u64 {
    144 * tx.inputs.len() as u64 + 40 + 164 * tx.outputs.len() as u64
}

fn build_cost_tx(witness_lens: &[usize], num_outputs: usize) -> Transaction {
    let inputs = witness_lens
        .iter()
        .enumerate()
        .map(|(index, witness_len)| TxInput {
            outpoint: initial_outpoint(10_000 + index as u64),
            witness: vec![0xA5; *witness_len],
        })
        .collect();
    let outputs = (0..num_outputs)
        .map(|index| tx_output_from_shape(OutputShape::new(2, 0), 0x80u8.wrapping_add(index as u8)))
        .collect();

    Transaction {
        version: 2,
        inputs,
        outputs,
        locktime: 0,
    }
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

fn record_tx_case(mut digest: Digest, case_index: usize, case: &TxCase) -> Digest {
    let config = config();
    let (utxo, mut projection) = build_initial_utxo(&case.utxo);
    let tx = build_transaction(&mut projection, &case.inputs, &case.outputs, 0x50);
    register_fresh_outputs(&mut projection, case.fresh_id, &tx);
    for id in &case.observed_ids {
        ensure_initial_projection(&mut projection, *id);
    }

    digest = digest.add_byte(0xB1);
    digest = digest.add_u64(case_index as u64);
    digest = digest.add_string(case.name);
    digest = digest.add_u64(case.height);
    digest = digest.add_u64(case.fresh_id);
    digest = digest.add_state(&case.observed_ids, &projection, &utxo);
    digest = digest.add_bool(has_duplicate_inputs(&tx));
    digest = digest.add_option_u64(sum_input_values(&utxo, &tx));
    digest = digest.add_u64(sum_output_values(&tx));
    digest = digest.add_bool(check_migration_rules(case.height, &tx, &utxo, &config));
    digest = digest.add_bool(check_no_frozen_inputs(case.height, &tx, &utxo, &config));
    digest = digest.add_bool(valid_tx(&utxo, &tx, case.height, &config));
    digest = digest.add_u64(structural_tx_cost(&tx));

    let mut post = utxo.clone();
    delta_tx(&mut post, &tx);
    digest.add_state(&case.observed_ids, &projection, &post)
}

fn record_block_case(mut digest: Digest, case_index: usize, case: &BlockCase) -> Digest {
    let config = config();
    let (utxo, projection, block) = build_block_case(case);

    digest = digest.add_byte(0xB2);
    digest = digest.add_u64(case_index as u64);
    digest = digest.add_string(case.name);
    digest = digest.add_u64(case.height);
    digest = digest.add_u64(case.fresh_id);
    digest = digest.add_state(&case.observed_ids, &projection, &utxo);

    let transition_result = apply_block_transitions(&utxo, &block, case.height, &config);
    let valid_result = validate_and_apply_block(&utxo, &block, case.height, &config);
    digest = digest.add_bool(transition_result.is_some());
    digest = digest.add_bool(check_block_cost(&block));
    digest = digest.add_bool(valid_block(&utxo, &block, case.height, &config));

    digest = match transition_result {
        None => digest.add_bool(false),
        Some(final_utxo) => {
            digest
                .add_bool(true)
                .add_state(&case.observed_ids, &projection, &final_utxo)
        }
    };

    match valid_result {
        None => digest.add_bool(false),
        Some(final_utxo) => {
            digest
                .add_bool(true)
                .add_state(&case.observed_ids, &projection, &final_utxo)
        }
    }
}

fn record_cost_case(mut digest: Digest, case_index: usize, case: &CostCase) -> Digest {
    let block: Block = case
        .shapes
        .iter()
        .map(|(witness_lens, num_outputs)| build_cost_tx(witness_lens, *num_outputs))
        .collect();

    digest = digest.add_byte(0xB3);
    digest = digest.add_u64(case_index as u64);
    digest = digest.add_string(case.name);
    digest = digest.add_u64(block.iter().map(cost_tx).sum());
    digest = digest.add_bool(check_block_cost(&block));

    for (tx, (witness_lens, num_outputs)) in block.iter().zip(case.shapes.iter()) {
        digest = digest.add_u64(witness_lens.len() as u64);
        for witness_len in witness_lens {
            digest = digest.add_u64(*witness_len as u64);
        }
        digest = digest.add_u64(*num_outputs as u64);
        digest = digest.add_u64(cost_tx(tx));
        digest = digest.add_u64(weight_tx(tx));
    }

    digest
}

fn main() {
    let tx_cases = tx_cases();
    let block_cases = block_cases();
    let cost_cases = cost_cases();

    let mut digest = Digest::new();
    for (case_index, case) in tx_cases.iter().enumerate() {
        digest = record_tx_case(digest, case_index, case);
    }
    for (case_index, case) in block_cases.iter().enumerate() {
        digest = record_block_case(digest, case_index, case);
    }
    for (case_index, case) in cost_cases.iter().enumerate() {
        digest = record_cost_case(digest, case_index, case);
    }

    println!("{{");
    println!("  \"model\": \"utxo-transition-refinement\",");
    println!("  \"tx_case_count\": {},", tx_cases.len());
    println!("  \"block_case_count\": {},", block_cases.len());
    println!("  \"cost_case_count\": {},", cost_cases.len());
    println!("  \"projection\": \"coq_nat_outpoint_to_rust_initial_or_fresh_output_id\",");
    println!(
        "  \"observed_functions\": [\"valid_tx_structural\", \"delta_tx\", \"apply_block_transitions_structural\", \"apply_valid_block_structural\", \"valid_block_structural\", \"cost_tx\", \"check_block_cost\"],"
    );
    println!("  \"hash_mod_1000000007\": {},", digest.h1);
    println!("  \"hash_mod_1000000009\": {}", digest.h2);
    println!("}}");
}
