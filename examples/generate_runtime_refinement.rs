//! Runtime txid and UTXO-store refinement summary.
//!
//! This executable validates two implementation boundaries that are deliberately
//! outside the Kani finite-map model:
//!
//! - `txid_preimage` and `compute_txid` are compared against an independent
//!   reference transcript and SHA-256 invocation.
//! - Runtime `UtxoSet`/`UtxoStore` behavior is compared extensionally
//!   against a deterministic vector-backed reference map through insert,
//!   replace, get, remove, canonical snapshot, and `delta_tx` transitions.
//!
//! This is release-binary refinement evidence for the deployed Rust runtime
//! path. It does not prove SHA-256 collision resistance, UTXO-store backend
//! internals, rustc, LLVM, linker, CPU, or OS correctness.

use sha2::{Digest as ShaDigest, Sha256};

use pq_witness_protocol::types::{
    canonical_utxo_entries, OutPoint, Output, Transaction, TxInput, TxOutput, UtxoSet,
};
use pq_witness_protocol::{compute_txid, delta_tx, txid_preimage};

const MODULUS_1: u64 = 1_000_000_007;
const MODULUS_2: u64 = 1_000_000_009;
const MULTIPLIER: u64 = 16_777_619;
const TXID_PREIMAGE_DOMAIN: &[u8] = b"BitcoinPQ:txid:v1";

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

    fn add_bytes(mut self, bytes: &[u8]) -> Self {
        self = self.add_u64(bytes.len() as u64);
        for byte in bytes {
            self = self.add_byte(*byte);
        }
        self
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

    fn add_outpoint(mut self, outpoint: &OutPoint) -> Self {
        self = self.add_bytes(&outpoint.txid);
        self.add_u64(u64::from(outpoint.vout))
    }

    fn add_output(self, output: &Output) -> Self {
        self.add_u64(u64::from(output.script_version))
            .add_bytes(&output.commitment)
            .add_u64(output.value)
    }

    fn add_snapshot(mut self, snapshot: &[(OutPoint, Output)]) -> Self {
        self = self.add_u64(snapshot.len() as u64);
        for (outpoint, output) in snapshot {
            self = self.add_outpoint(outpoint).add_output(output);
        }
        self
    }
}

#[derive(Clone, Default)]
struct ReferenceUtxo {
    entries: Vec<(OutPoint, Output)>,
}

impl ReferenceUtxo {
    fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    fn insert(&mut self, outpoint: OutPoint, output: Output) -> Option<Output> {
        if let Some((_, existing_output)) = self
            .entries
            .iter_mut()
            .find(|(existing_outpoint, _)| *existing_outpoint == outpoint)
        {
            return Some(std::mem::replace(existing_output, output));
        }
        self.entries.push((outpoint, output));
        None
    }

    fn get(&self, outpoint: &OutPoint) -> Option<&Output> {
        self.entries
            .iter()
            .find(|(existing_outpoint, _)| existing_outpoint == outpoint)
            .map(|(_, output)| output)
    }

    fn remove(&mut self, outpoint: &OutPoint) -> Option<Output> {
        let index = self
            .entries
            .iter()
            .position(|(existing_outpoint, _)| existing_outpoint == outpoint)?;
        Some(self.entries.remove(index).1)
    }

    fn snapshot(&self) -> Vec<(OutPoint, Output)> {
        let mut entries = self.entries.clone();
        entries.sort_by(|(left, _), (right, _)| left.cmp(right));
        entries
    }

    fn delta_tx(&mut self, tx: &Transaction) {
        for input in &tx.inputs {
            self.remove(&input.outpoint);
        }

        let txid = reference_compute_txid(tx);
        for (vout, output) in tx.outputs.iter().enumerate() {
            self.insert(
                OutPoint {
                    txid,
                    vout: vout as u32,
                },
                Output {
                    script_version: output.script_version,
                    commitment: output.commitment,
                    value: output.value,
                },
            );
        }
    }
}

fn reference_txid_preimage(tx: &Transaction) -> Vec<u8> {
    let mut preimage = Vec::new();

    preimage.extend_from_slice(TXID_PREIMAGE_DOMAIN);
    preimage.extend_from_slice(&tx.version.to_le_bytes());
    preimage.extend_from_slice(&(tx.inputs.len() as u64).to_le_bytes());

    for input in &tx.inputs {
        preimage.extend_from_slice(&input.outpoint.txid);
        preimage.extend_from_slice(&input.outpoint.vout.to_le_bytes());
    }

    preimage.extend_from_slice(&(tx.outputs.len() as u64).to_le_bytes());

    for output in &tx.outputs {
        preimage.push(output.script_version);
        preimage.extend_from_slice(&output.commitment);
        preimage.extend_from_slice(&output.value.to_le_bytes());
    }

    preimage.extend_from_slice(&tx.locktime.to_le_bytes());
    preimage
}

fn reference_compute_txid(tx: &Transaction) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(reference_txid_preimage(tx));
    hasher.finalize().into()
}

fn commitment(seed: u8) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (index, byte) in out.iter_mut().enumerate() {
        *byte = seed
            .wrapping_add((index as u8).wrapping_mul(17))
            .wrapping_add((index / 5) as u8);
    }
    out
}

fn outpoint(seed: u8, vout: u32) -> OutPoint {
    let mut txid = [0u8; 32];
    for (index, byte) in txid.iter_mut().enumerate() {
        *byte = seed
            .wrapping_add((index as u8).wrapping_mul(29))
            .wrapping_add((index / 3) as u8);
    }
    OutPoint { txid, vout }
}

fn output(script_version: u8, seed: u8, value: u64) -> Output {
    Output {
        script_version,
        commitment: commitment(seed),
        value,
    }
}

fn tx_output(script_version: u8, seed: u8, value: u64) -> TxOutput {
    TxOutput {
        script_version,
        commitment: commitment(seed),
        value,
    }
}

fn input(outpoint: OutPoint, witness_seed: u8, witness_len: usize) -> TxInput {
    TxInput {
        outpoint,
        witness: vec![witness_seed; witness_len],
    }
}

fn tx_cases() -> Vec<(&'static str, Transaction)> {
    vec![
        (
            "empty",
            Transaction {
                version: 2,
                inputs: vec![],
                outputs: vec![],
                locktime: 0,
            },
        ),
        (
            "single-input-output",
            Transaction {
                version: 2,
                inputs: vec![input(outpoint(1, 0), 0xAA, 2)],
                outputs: vec![tx_output(2, 0x10, 50_000)],
                locktime: 0,
            },
        ),
        (
            "multi-input-output",
            Transaction {
                version: 3,
                inputs: vec![
                    input(outpoint(2, 1), 0xBB, 3),
                    input(outpoint(3, 7), 0xCC, 4),
                ],
                outputs: vec![tx_output(0, 0x20, 25_000), tx_output(2, 0x21, 24_000)],
                locktime: 144,
            },
        ),
        (
            "count-delimited-many-inputs",
            Transaction {
                version: 4,
                inputs: (0..41)
                    .map(|index| input(outpoint(index as u8, index as u32), 0xDD, 1))
                    .collect(),
                outputs: vec![],
                locktime: 500,
            },
        ),
        (
            "count-delimited-many-outputs",
            Transaction {
                version: 4,
                inputs: vec![],
                outputs: (0..36)
                    .map(|index| tx_output(2, index as u8, 1_000 + index as u64))
                    .collect(),
                locktime: 500,
            },
        ),
    ]
}

fn assert_runtime_matches_reference(
    digest: Digest,
    label: &str,
    runtime: &UtxoSet,
    reference: &ReferenceUtxo,
) -> Digest {
    let runtime_snapshot = canonical_utxo_entries(runtime);
    let reference_snapshot = reference.snapshot();
    assert_eq!(
        runtime_snapshot, reference_snapshot,
        "runtime UTXO snapshot diverged from reference for {label}"
    );
    digest
        .add_string(label)
        .add_snapshot(&runtime_snapshot)
        .add_bool(true)
}

fn record_txid_refinement(mut digest: Digest) -> Digest {
    let cases = tx_cases();
    digest = digest.add_u64(cases.len() as u64);

    for (name, tx) in &cases {
        let runtime_preimage = txid_preimage(tx);
        let reference_preimage = reference_txid_preimage(tx);
        assert_eq!(
            runtime_preimage, reference_preimage,
            "txid preimage mismatch for {name}"
        );

        let runtime_txid = compute_txid(tx);
        let reference_txid = reference_compute_txid(tx);
        assert_eq!(runtime_txid, reference_txid, "txid mismatch for {name}");

        digest = digest
            .add_string(name)
            .add_bytes(&runtime_preimage)
            .add_bytes(&runtime_txid);
    }

    let many_inputs = &cases[3].1;
    let many_outputs = &cases[4].1;
    assert_eq!(
        many_inputs.inputs.len() * (32 + 4),
        many_outputs.outputs.len() * (1 + 32 + 8)
    );
    assert_ne!(txid_preimage(many_inputs), txid_preimage(many_outputs));

    digest.add_bool(true)
}

fn record_map_refinement(mut digest: Digest) -> Digest {
    let mut runtime = UtxoSet::new();
    let mut reference = ReferenceUtxo::new();

    let op1 = outpoint(0x10, 0);
    let op2 = outpoint(0x20, 1);
    let op3 = outpoint(0x30, 2);
    let missing = outpoint(0xFE, 0);

    assert_eq!(
        runtime.insert(op2.clone(), output(2, 0x42, 42)),
        reference.insert(op2.clone(), output(2, 0x42, 42))
    );
    digest = assert_runtime_matches_reference(digest, "insert-op2", &runtime, &reference);

    assert_eq!(
        runtime.insert(op1.clone(), output(0, 0x41, 41)),
        reference.insert(op1.clone(), output(0, 0x41, 41))
    );
    digest = assert_runtime_matches_reference(digest, "insert-op1", &runtime, &reference);

    assert_eq!(
        runtime.insert(op2.clone(), output(2, 0x52, 52)),
        reference.insert(op2.clone(), output(2, 0x52, 52))
    );
    digest = assert_runtime_matches_reference(digest, "replace-op2", &runtime, &reference);

    assert_eq!(runtime.get(&op1), reference.get(&op1));
    assert_eq!(runtime.get(&missing), reference.get(&missing));
    digest = digest.add_bool(true);

    assert_eq!(runtime.remove(&missing), reference.remove(&missing));
    digest = assert_runtime_matches_reference(digest, "remove-missing", &runtime, &reference);

    assert_eq!(runtime.remove(&op2), reference.remove(&op2));
    digest = assert_runtime_matches_reference(digest, "remove-op2", &runtime, &reference);

    assert_eq!(
        runtime.insert(op3.clone(), output(0, 0x43, 70)),
        reference.insert(op3.clone(), output(0, 0x43, 70))
    );
    digest = assert_runtime_matches_reference(digest, "insert-op3", &runtime, &reference);

    let tx = Transaction {
        version: 2,
        inputs: vec![input(op1.clone(), 0xAA, 2)],
        outputs: vec![tx_output(2, 0x60, 30), tx_output(0, 0x61, 10)],
        locktime: 7,
    };

    delta_tx(&mut runtime, &tx);
    reference.delta_tx(&tx);
    digest = assert_runtime_matches_reference(digest, "delta-tx", &runtime, &reference);

    assert!(!runtime.contains_key(&op1));
    assert_eq!(runtime.contains_key(&op3), reference.get(&op3).is_some());

    digest.add_bool(true)
}

fn main() {
    let mut digest = Digest::new();
    digest = record_txid_refinement(digest);
    digest = record_map_refinement(digest);

    println!("{{");
    println!("  \"model\": \"runtime-txid-utxo-map-refinement\",");
    println!("  \"txid_case_count\": {},", tx_cases().len());
    println!("  \"map_operation_count\": 8,");
    println!(
        "  \"observed_functions\": [\"txid_preimage\", \"compute_txid\", \"canonical_utxo_entries\", \"UtxoSet::insert\", \"UtxoSet::get\", \"UtxoSet::remove\", \"delta_tx\"],"
    );
    println!("  \"hash_mod_1000000007\": {},", digest.h1);
    println!("  \"hash_mod_1000000009\": {},", digest.h2);
    println!("  \"status\": \"match\"");
    println!("}}");
}
