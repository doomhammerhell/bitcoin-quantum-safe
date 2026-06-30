//! Rust-side txid preimage refinement summary.
//!
//! This executable observes `src/lib.rs::txid_preimage` over the same
//! deterministic matrix as the Coq-extracted harness. It compares the
//! pre-hash transcript boundary; SHA-256 remains covered by the separate
//! runtime txid/hash wiring validation.

use pq_witness_protocol::txid_preimage;
use pq_witness_protocol::types::{OutPoint, Transaction, TxInput, TxOutput};

const MODULUS_1: u64 = 1_000_000_007;
const MODULUS_2: u64 = 1_000_000_009;
const MULTIPLIER: u64 = 16_777_619;
const TXID_DOMAIN_LEN: usize = 17;

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

    fn add_bytes(mut self, bytes: &[u8]) -> Self {
        self = self.add_u64(bytes.len() as u64);
        for byte in bytes {
            self = self.add_byte(*byte);
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

fn record_case(mut digest: Digest, case_index: usize, name: &str, tx: &Transaction) -> Digest {
    let preimage = txid_preimage(tx);
    let expected_len =
        TXID_DOMAIN_LEN + 4 + 8 + tx.inputs.len() * 36 + 8 + tx.outputs.len() * 41 + 4;
    assert_eq!(
        preimage.len(),
        expected_len,
        "txid preimage length mismatch for {name}"
    );

    digest = digest.add_byte(0xB5);
    digest = digest.add_u64(case_index as u64);
    digest = digest.add_string(name);
    digest = digest.add_u64(tx.version as u64);
    digest = digest.add_u64(tx.locktime as u64);
    digest = digest.add_u64(tx.inputs.len() as u64);
    digest = digest.add_u64(tx.outputs.len() as u64);
    digest = digest.add_bytes(&preimage);
    digest.add_bool(preimage.len() == expected_len)
}

fn main() {
    let cases = tx_cases();
    let digest = cases
        .iter()
        .enumerate()
        .fold(Digest::new(), |digest, (case_index, (name, tx))| {
            record_case(digest, case_index, name, tx)
        });

    println!("{{");
    println!("  \"model\": \"txid-preimage-refinement\",");
    println!("  \"case_count\": {},", cases.len());
    println!("  \"domain_len\": {},", TXID_DOMAIN_LEN);
    println!("  \"observed_functions\": [\"txid_preimage\"],");
    println!("  \"hash_mod_1000000007\": {},", digest.h1);
    println!("  \"hash_mod_1000000009\": {}", digest.h2);
    println!("}}");
}
