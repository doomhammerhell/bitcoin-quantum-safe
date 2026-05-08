//! Golden Vector Generator for PO-8 Verification
//!
//! This executable produces canonical test vectors from the Rust implementation
//! that must match the Coq-extracted OCaml implementation byte-for-byte.
//!
//! Usage: cargo run --example generate_golden_vectors > rust_vectors.json

use pq_witness_protocol::encoding::{encode_varint, serialize_witness};
use sha2::{Digest, Sha256};

/// A golden test vector
#[derive(Debug, serde::Serialize)]
struct GoldenVector {
    name: String,
    pk_len: usize,
    pk: String, // hex-encoded
    sig_len: usize,
    sig: String,     // hex-encoded
    witness: String, // hex-encoded
}

fn bytes_to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

fn repeat_byte(byte: u8, n: usize) -> Vec<u8> {
    vec![byte; n]
}

fn main() {
    let mut vectors = Vec::new();

    // Vector 1: Small witness (single-byte varints)
    let pk_small = vec![0xAB, 0xCD, 0xEF];
    let sig_small = vec![0x12, 0x34];
    let w1 = serialize_witness(&pk_small, &sig_small);
    vectors.push(GoldenVector {
        name: "small".to_string(),
        pk_len: pk_small.len(),
        pk: bytes_to_hex(&pk_small),
        sig_len: sig_small.len(),
        sig: bytes_to_hex(&sig_small),
        witness: bytes_to_hex(&w1),
    });

    // Vector 2: ML-DSA-44 sized witness
    // pk_len = 1312 requires 0xFD prefix
    let pk_ml = repeat_byte(0x42, 1312);
    let sig_ml = repeat_byte(0x99, 2420);
    let w2 = serialize_witness(&pk_ml, &sig_ml);
    vectors.push(GoldenVector {
        name: "ml_dsa_44".to_string(),
        pk_len: pk_ml.len(),
        pk: bytes_to_hex(&pk_ml),
        sig_len: sig_ml.len(),
        sig: bytes_to_hex(&sig_ml),
        witness: bytes_to_hex(&w2),
    });

    // Vector 3: SLH-DSA-128s sized witness
    // pk_len = 32 (single byte), sig_len = 7856 requires 0xFD prefix
    let pk_slh = repeat_byte(0x55, 32);
    let sig_slh = repeat_byte(0x77, 7856);
    let w3 = serialize_witness(&pk_slh, &sig_slh);
    vectors.push(GoldenVector {
        name: "slh_dsa_128s".to_string(),
        pk_len: pk_slh.len(),
        pk: bytes_to_hex(&pk_slh),
        sig_len: sig_slh.len(),
        sig: bytes_to_hex(&sig_slh),
        witness: bytes_to_hex(&w3),
    });

    // Vector 4: Empty witness (edge case)
    let pk_empty: Vec<u8> = vec![];
    let sig_empty: Vec<u8> = vec![];
    let w4 = serialize_witness(&pk_empty, &sig_empty);
    vectors.push(GoldenVector {
        name: "empty".to_string(),
        pk_len: pk_empty.len(),
        pk: bytes_to_hex(&pk_empty),
        sig_len: sig_empty.len(),
        sig: bytes_to_hex(&sig_empty),
        witness: bytes_to_hex(&w4),
    });

    // Vector 5: Exactly 253 bytes (largest single-byte varint boundary)
    let pk_253 = repeat_byte(0xAA, 253);
    let sig_253 = repeat_byte(0xBB, 253);
    let w5 = serialize_witness(&pk_253, &sig_253);
    vectors.push(GoldenVector {
        name: "boundary_253".to_string(),
        pk_len: pk_253.len(),
        pk: bytes_to_hex(&pk_253),
        sig_len: sig_253.len(),
        sig: bytes_to_hex(&sig_253),
        witness: bytes_to_hex(&w5),
    });

    // Vector 6: Exactly 254 bytes (smallest two-byte varint)
    let pk_254 = repeat_byte(0xCC, 254);
    let sig_254 = repeat_byte(0xDD, 254);
    let w6 = serialize_witness(&pk_254, &sig_254);
    vectors.push(GoldenVector {
        name: "boundary_254".to_string(),
        pk_len: pk_254.len(),
        pk: bytes_to_hex(&pk_254),
        sig_len: sig_254.len(),
        sig: bytes_to_hex(&sig_254),
        witness: bytes_to_hex(&w6),
    });

    // Vector 7: Large (65535 bytes - largest two-byte varint)
    let pk_65535 = repeat_byte(0xEE, 65535);
    let sig_1 = vec![0xFF];
    let w7 = serialize_witness(&pk_65535, &sig_1);
    vectors.push(GoldenVector {
        name: "large_65535".to_string(),
        pk_len: pk_65535.len(),
        pk: bytes_to_hex(&pk_65535),
        sig_len: sig_1.len(),
        sig: bytes_to_hex(&sig_1),
        witness: bytes_to_hex(&w7),
    });

    // Vector 8: Very large (65536 bytes, requires 0xFE prefix)
    let pk_65536 = repeat_byte(0x11, 65536);
    let sig_2 = vec![0x22, 0x33];
    let w8 = serialize_witness(&pk_65536, &sig_2);
    vectors.push(GoldenVector {
        name: "very_large_65536".to_string(),
        pk_len: pk_65536.len(),
        pk: bytes_to_hex(&pk_65536),
        sig_len: sig_2.len(),
        sig: bytes_to_hex(&sig_2),
        witness: bytes_to_hex(&w8),
    });

    // Output JSON
    println!("{}", serde_json::to_string_pretty(&vectors).unwrap());
}
