//! Bounded witness-level refinement summary for PO-8.
//!
//! This executable computes the Rust-side transcript for the single-signature
//! witness serializer, byte-level parser, consensus-domain parser, trace hook,
//! and canonicality predicates. The Coq side computes the same transcript from
//! extracted OCaml; CI compares the JSON objects exactly.

use pq_witness_protocol::encoding::{
    is_canonical_consensus_witness, is_canonical_witness, parse_consensus_witness, parse_witness,
    parse_witness_trace, serialize_witness,
};

const MODULUS_1: u64 = 1_000_000_007;
const MODULUS_2: u64 = 1_000_000_009;
const MULTIPLIER: u64 = 16_777_619;

const CANONICAL_LENGTHS: &[usize] = &[
    0, 1, 2, 3, 4, 31, 32, 33, 100, 251, 252, 253, 254, 255, 256, 512, 1000, 1312, 2420, 7856,
    8000, 12000, 15990, 15991, 15992, 15993, 15994, 15995, 15996, 15997, 15998, 15999, 16000,
    65535,
];
const SYMBOLIC_ALPHABET: &[u8] = &[0, 1, 2, 3, 4, 31, 32, 33, 252, 253];
const SYMBOLIC_MAX_LEN: usize = 5;

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

    fn add_trace(mut self, trace: &[u64]) -> Self {
        self = self.add_u64(trace.len() as u64);
        for event in trace {
            self = self.add_u64(*event);
        }
        self
    }

    fn add_parse_result(self, result: Option<(Vec<u8>, Vec<u8>)>) -> Self {
        match result {
            None => self.add_byte(0),
            Some((pk, sig)) => self.add_byte(1).add_bytes(&pk).add_bytes(&sig),
        }
    }
}

fn byte_at(seed: usize, i: usize) -> u8 {
    ((seed + (i * 131) + ((i / 7) * 17) + (i & 31)) & 0xff) as u8
}

fn bytes(len: usize, seed: usize) -> Vec<u8> {
    (0..len).map(|i| byte_at(seed, i)).collect()
}

fn record_observation(mut digest: Digest, tag: u8, witness: &[u8]) -> Digest {
    let (trace, traced_result) = parse_witness_trace(witness);
    digest = digest.add_byte(tag);
    digest = digest.add_bytes(witness);
    digest = digest.add_parse_result(parse_witness(witness));
    digest = digest.add_parse_result(parse_consensus_witness(witness));
    digest = digest.add_parse_result(traced_result);
    digest = digest.add_trace(&trace);
    digest = digest.add_bool(is_canonical_witness(witness));
    digest.add_bool(is_canonical_consensus_witness(witness))
}

fn record_canonical_case(
    mut digest: Digest,
    case_index: usize,
    pk_len: usize,
    sig_len: usize,
) -> Digest {
    let pk = bytes(pk_len, 0x31 + case_index);
    let sig = bytes(sig_len, 0xA7 + case_index);
    let witness = serialize_witness(&pk, &sig);

    digest = digest.add_byte(0xC1);
    digest = digest.add_u64(case_index as u64);
    digest = digest.add_u64(pk_len as u64);
    digest = digest.add_u64(sig_len as u64);
    digest = digest.add_bytes(&pk);
    digest = digest.add_bytes(&sig);
    record_observation(digest, 0xC2, &witness)
}

fn malformed_cases() -> Vec<Vec<u8>> {
    let mut valid_small = serialize_witness(&[1, 2, 3], &[0xAA, 0xBB]);
    valid_small.push(255);

    vec![
        vec![],
        vec![0, 1, 0xAA],
        vec![1, 0xAA, 0],
        vec![10, 1, 2, 3],
        vec![1, 0xAA],
        vec![253],
        vec![253, 0],
        vec![253, 1, 0, 0xAA, 1, 0xBB],
        vec![1, 0xAA, 253, 1, 0, 0xBB],
        valid_small,
        vec![1, 0xAA, 3, 0xBB],
        vec![253, 253, 0, 0xAA],
        vec![1, 0xAA, 253, 253, 0, 0xBB],
        vec![254],
        vec![255],
    ]
}

fn fold_canonical_matrix(mut digest: Digest) -> Digest {
    let mut case_index = 0usize;
    for &pk_len in CANONICAL_LENGTHS {
        for &sig_len in CANONICAL_LENGTHS {
            digest = record_canonical_case(digest, case_index, pk_len, sig_len);
            case_index += 1;
        }
    }
    digest
}

fn fold_malformed(mut digest: Digest) -> Digest {
    for (case_index, witness) in malformed_cases().iter().enumerate() {
        digest = digest.add_byte(0xE1);
        digest = digest.add_u64(case_index as u64);
        digest = record_observation(digest, 0xE2, witness);
    }
    digest
}

fn fold_symbolic_words<F>(len: usize, prefix: &mut Vec<u8>, digest: Digest, f: &mut F) -> Digest
where
    F: FnMut(Digest, &[u8]) -> Digest,
{
    if len == 0 {
        return f(digest, prefix);
    }

    let mut current = digest;
    for &byte in SYMBOLIC_ALPHABET {
        prefix.push(byte);
        current = fold_symbolic_words(len - 1, prefix, current, f);
        prefix.pop();
    }
    current
}

fn fold_symbolic_state_space(mut digest: Digest) -> Digest {
    let mut case_index = 0usize;

    for len in 0..=SYMBOLIC_MAX_LEN {
        let mut prefix = Vec::with_capacity(len);
        digest = fold_symbolic_words(len, &mut prefix, digest, &mut |mut inner, witness| {
            inner = inner.add_byte(0xF1);
            inner = inner.add_u64(case_index as u64);
            inner = inner.add_u64(len as u64);
            case_index += 1;
            record_observation(inner, 0xF2, witness)
        });
    }

    digest
}

fn symbolic_case_count() -> usize {
    (0..=SYMBOLIC_MAX_LEN)
        .map(|len| SYMBOLIC_ALPHABET.len().pow(len as u32))
        .sum()
}

fn main() {
    let canonical_length_count = CANONICAL_LENGTHS.len();
    let canonical_pair_cases = canonical_length_count * canonical_length_count;
    let malformed_case_count = malformed_cases().len();
    let symbolic_case_count = symbolic_case_count();
    let digest = fold_symbolic_state_space(fold_malformed(fold_canonical_matrix(Digest::new())));

    println!("{{");
    println!("  \"model\": \"single-sig-witness-u16-refinement-matrix\",");
    println!("  \"domain_min\": 0,");
    println!("  \"domain_max\": 65535,");
    println!("  \"max_consensus_witness_size\": 16000,");
    println!(
        "  \"canonical_length_representatives\": {},",
        canonical_length_count
    );
    println!("  \"canonical_pair_cases\": {},", canonical_pair_cases);
    println!("  \"malformed_cases\": {},", malformed_case_count);
    println!("  \"symbolic_alphabet_size\": {},", SYMBOLIC_ALPHABET.len());
    println!("  \"symbolic_max_len\": {},", SYMBOLIC_MAX_LEN);
    println!("  \"symbolic_state_cases\": {},", symbolic_case_count);
    println!(
        "  \"observed_functions\": [\"serialize_witness\", \"parse_witness\", \"parse_consensus_witness\", \"parse_witness_trace\", \"is_canonical_witness\", \"is_canonical_consensus_witness\"],"
    );
    println!("  \"hash_mod_1000000007\": {},", digest.h1);
    println!("  \"hash_mod_1000000009\": {}", digest.h2);
    println!("}}");
}
