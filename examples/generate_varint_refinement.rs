//! Exhaustive bounded varint refinement summary for PO-8.
//!
//! This executable computes the Rust-side summary for the complete Coq-modeled
//! CompactSize domain, 0..=65535. The Coq side computes the same summary from
//! extracted OCaml; CI compares the JSON objects exactly.

use pq_witness_protocol::encoding::{decode_varint, encode_varint};

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

    fn add_decode_result(self, result: Option<(u64, usize)>) -> Self {
        match result {
            None => self.add_byte(0),
            Some((value, consumed)) => self.add_byte(1).add_u64(value).add_u64(consumed as u64),
        }
    }
}

fn record_encoded(mut digest: Digest, value: u64, encoded: &[u8]) -> Digest {
    digest = digest
        .add_byte(0xE1)
        .add_u64(value)
        .add_u64(encoded.len() as u64);

    for byte in encoded {
        digest = digest.add_byte(*byte);
    }

    digest
}

fn record_decoded(digest: Digest, tag: u8, bytes: &[u8]) -> Digest {
    digest
        .add_byte(tag)
        .add_u64(bytes.len() as u64)
        .add_decode_result(decode_varint(bytes))
}

fn main() {
    let mut digest = Digest::new();

    for value in 0..=65_535u64 {
        let encoded = encode_varint(value);
        digest = record_encoded(digest, value, &encoded);
        digest = record_decoded(digest, 0xD1, &encoded);

        let mut trailing = encoded;
        trailing.extend_from_slice(&[17, 34, 255]);
        digest = record_decoded(digest, 0xD2, &trailing);
    }

    for value in 0..=252u64 {
        let noncanonical = [0xFD, value as u8, (value >> 8) as u8];
        digest = record_decoded(digest, 0xB1, &noncanonical);
    }

    for bytes in [&[0xFD][..], &[0xFD, 0x00][..], &[0xFE][..], &[0xFF][..]] {
        digest = record_decoded(digest, 0xB2, bytes);
    }

    println!("{{");
    println!("  \"model\": \"bitcoin-compact-size-u16\",");
    println!("  \"domain_min\": 0,");
    println!("  \"domain_max\": 65535,");
    println!("  \"encode_cases\": 65536,");
    println!("  \"decode_cases\": 65536,");
    println!("  \"trailing_decode_cases\": 65536,");
    println!("  \"noncanonical_fd_cases\": 253,");
    println!("  \"truncated_or_unsupported_cases\": 4,");
    println!("  \"hash_mod_1000000007\": {},", digest.h1);
    println!("  \"hash_mod_1000000009\": {}", digest.h2);
    println!("}}");
}
