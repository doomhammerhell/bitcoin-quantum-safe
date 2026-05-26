//! Rust-side PO-4 sighash transcript refinement summary.
//!
//! This executable observes the deterministic serialization boundary of
//! `src/sighash.rs`: outpoint serialization, output serialization,
//! spent-output serialization, and final preimage assembly with supplied
//! 32-byte sub-hashes. The Coq side computes the same structural transcript
//! from extracted functions; CI compares the JSON summaries exactly.

use pq_witness_protocol::sighash::{
    serialize_sighash_outpoints, serialize_sighash_outputs, serialize_sighash_spent_output,
    sighash_v2_preimage_with_hashes, SIGHASH_V2_PREIMAGE_LEN,
};
use pq_witness_protocol::types::{OutPoint, Output, Transaction, TxInput, TxOutput};

const MODULUS_1: u64 = 1_000_000_007;
const MODULUS_2: u64 = 1_000_000_009;
const MULTIPLIER: u64 = 16_777_619;

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

    fn add_u64(mut self, value: u64) -> Self {
        for byte in value.to_le_bytes() {
            self = self.add_byte(byte);
        }
        self
    }

    fn add_bool(self, value: bool) -> Self {
        self.add_byte(u8::from(value))
    }

    fn add_bytes(mut self, bytes: &[u8]) -> Self {
        self = self.add_u64(bytes.len() as u64);
        for byte in bytes {
            self = self.add_byte(*byte);
        }
        self
    }
}

struct Case {
    name: &'static str,
    tx: Transaction,
    input_index: usize,
    spent_output: Output,
    hash_outpoints: [u8; 32],
    hash_outputs: [u8; 32],
}

fn byte_at(seed: usize, i: usize) -> u8 {
    ((seed + (i * 131) + ((i / 7) * 17) + (i & 31)) & 0xff) as u8
}

fn bytes(len: usize, seed: usize) -> Vec<u8> {
    (0..len).map(|i| byte_at(seed, i)).collect()
}

fn bytes32(seed: usize) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = byte_at(seed, i);
    }
    out
}

fn input(txid_seed: usize, vout: u32, witness_seed: usize, witness_len: usize) -> TxInput {
    TxInput {
        outpoint: OutPoint {
            txid: bytes32(txid_seed),
            vout,
        },
        witness: bytes(witness_len, witness_seed),
    }
}

fn tx_output(script_version: u8, commitment_seed: usize, value: u64) -> TxOutput {
    TxOutput {
        script_version,
        commitment: bytes32(commitment_seed),
        value,
    }
}

fn spent_output(script_version: u8, commitment_seed: usize, value: u64) -> Output {
    Output {
        script_version,
        commitment: bytes32(commitment_seed),
        value,
    }
}

fn cases() -> Vec<Case> {
    vec![
        Case {
            name: "single-input-single-output",
            tx: Transaction {
                version: 2,
                inputs: vec![input(0x10, 0, 0xA0, 1)],
                outputs: vec![tx_output(2, 0x20, 1_000)],
                locktime: 0,
            },
            input_index: 0,
            spent_output: spent_output(2, 0x30, 2_000),
            hash_outpoints: bytes32(0x40),
            hash_outputs: bytes32(0x50),
        },
        Case {
            name: "two-inputs-two-outputs-index-one",
            tx: Transaction {
                version: 2,
                inputs: vec![input(0x11, 0, 0xA1, 2), input(0x12, 1, 0xA2, 3)],
                outputs: vec![tx_output(2, 0x21, 50_000), tx_output(1, 0x22, 25_000)],
                locktime: 100,
            },
            input_index: 1,
            spent_output: spent_output(2, 0x31, 75_000),
            hash_outpoints: bytes32(0x41),
            hash_outputs: bytes32(0x51),
        },
        Case {
            name: "little-endian-boundaries",
            tx: Transaction {
                version: 0xA1B2_C3D4,
                inputs: vec![
                    input(0x13, 0xDEAD_BEEF, 0xA3, 4),
                    input(0x14, 0x0102_0304, 0xA4, 5),
                ],
                outputs: vec![tx_output(255, 0x23, 281_474_976_710_655)],
                locktime: 0xFEDC_BA98,
            },
            input_index: 0,
            spent_output: spent_output(254, 0x32, 9_007_199_254_740_991),
            hash_outpoints: bytes32(0x42),
            hash_outputs: bytes32(0x52),
        },
        Case {
            name: "zero-outputs",
            tx: Transaction {
                version: 0,
                inputs: vec![input(0x15, 2, 0xA5, 0)],
                outputs: vec![],
                locktime: 42,
            },
            input_index: 0,
            spent_output: spent_output(0, 0x33, 0),
            hash_outpoints: bytes32(0x43),
            hash_outputs: bytes32(0x53),
        },
        Case {
            name: "witness-bytes-excluded",
            tx: Transaction {
                version: 3,
                inputs: vec![input(0x16, 7, 0xA6, 128), input(0x17, 8, 0xA7, 64)],
                outputs: vec![tx_output(2, 0x24, 4_000_000)],
                locktime: 500_000,
            },
            input_index: 1,
            spent_output: spent_output(2, 0x34, 4_500_000),
            hash_outpoints: bytes32(0x44),
            hash_outputs: bytes32(0x54),
        },
    ]
}

fn record_case(mut digest: Digest, case_index: usize, case: &Case) -> Digest {
    let outpoints = serialize_sighash_outpoints(&case.tx);
    let outputs = serialize_sighash_outputs(&case.tx);
    let spent = serialize_sighash_spent_output(&case.spent_output);
    let preimage = sighash_v2_preimage_with_hashes(
        &case.tx,
        case.input_index,
        &case.spent_output,
        &case.hash_outpoints,
        &case.hash_outputs,
    );

    assert_eq!(preimage.len(), SIGHASH_V2_PREIMAGE_LEN);

    digest = digest.add_byte(0xA1);
    digest = digest.add_u64(case_index as u64);
    digest = digest.add_bytes(case.name.as_bytes());
    digest = digest.add_u64(case.tx.version as u64);
    digest = digest.add_u64(case.tx.locktime as u64);
    digest = digest.add_u64(case.input_index as u64);
    digest = digest.add_u64(case.tx.inputs.len() as u64);
    digest = digest.add_u64(case.tx.outputs.len() as u64);
    digest = digest.add_bytes(&outpoints);
    digest = digest.add_bytes(&outputs);
    digest = digest.add_bytes(&spent);
    digest = digest.add_bytes(&case.hash_outpoints);
    digest = digest.add_bytes(&case.hash_outputs);
    digest = digest.add_bytes(&preimage);
    digest.add_bool(preimage.len() == SIGHASH_V2_PREIMAGE_LEN)
}

fn main() {
    let cases = cases();
    let digest = cases
        .iter()
        .enumerate()
        .fold(Digest::new(), |digest, (i, case)| {
            record_case(digest, i, case)
        });

    println!("{{");
    println!("  \"model\": \"sighash-v2-transcript-refinement\",");
    println!("  \"case_count\": {},", cases.len());
    println!("  \"preimage_len\": {},", SIGHASH_V2_PREIMAGE_LEN);
    println!(
        "  \"observed_functions\": [\"serialize_sighash_outpoints\", \"serialize_sighash_outputs\", \"serialize_sighash_spent_output\", \"sighash_v2_preimage_with_hashes\"],"
    );
    println!("  \"hash_mod_1000000007\": {},", digest.h1);
    println!("  \"hash_mod_1000000009\": {}", digest.h2);
    println!("}}");
}
