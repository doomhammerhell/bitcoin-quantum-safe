//! PO-8: Bounded Implementation Correspondence via Golden Vectors
//!
//! This test validates that the Rust witness encoding matches the
//! Coq-extracted witness serializer byte-for-byte for the current formal
//! varint domain.
//!
//! Golden vectors are canonical test cases that exercise:
//! - Single-byte varints (values 0-252)
//! - Two-byte varints with 0xFD prefix (253-65535)
//! - Edge cases (empty witnesses, boundary values)
//!
//! Rust-only tests cover the 0xFE and 0xFF CompactSize ranges; those ranges are
//! outside the current Coq varint proof boundary for general-purpose CompactSize.
//! The consensus witness-size guard keeps accepted witness components inside the
//! modeled u16 domain while MAX_WITNESS_SIZE remains below 65535.
//!
//! Requirements: PO-8 (Implementation Correspondence)
//! Artifacts: Coq extraction → OCaml vector harness → JSON → Rust comparison

use pq_witness_protocol::encoding::{
    is_canonical_consensus_witness, parse_consensus_witness, parse_witness, serialize_witness,
};
use pq_witness_protocol::params::MAX_WITNESS_SIZE;

/// A golden test vector
#[derive(Debug, serde::Deserialize)]
struct GoldenVector {
    name: String,
    pk_len: usize,
    pk: String, // hex-encoded
    sig_len: usize,
    sig: String,     // hex-encoded
    witness: String, // hex-encoded (expected output)
}

/// Convert hex string to bytes
fn hex_to_bytes(hex: &str) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(hex.len() / 2);
    let mut chars = hex.chars();
    while let (Some(c1), Some(c2)) = (chars.next(), chars.next()) {
        let byte = u8::from_str_radix(&format!("{}{}", c1, c2), 16).unwrap();
        bytes.push(byte);
    }
    bytes
}

/// Convert bytes to hex string
fn bytes_to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

/// Load golden vectors from JSON file (embedded at compile time for hermetic tests)
fn load_golden_vectors() -> Vec<GoldenVector> {
    // For CI/local runs after extraction: load generated vectors from disk.
    // For hermetic cargo test: embed the checked-in bounded Coq vector baseline.
    let json_data =
        if let Ok(data) = std::fs::read_to_string("formal/coq/extraction/coq_vectors.json") {
            data
        } else {
            include_str!("../formal/coq/extraction/coq_vectors.json").to_string()
        };

    serde_json::from_str(&json_data).expect("Failed to parse golden vectors JSON")
}

/// Test that Rust witness serialization matches Coq/OCaml golden vectors
#[test]
fn po8_golden_vectors_byte_correspondence() {
    let vectors = load_golden_vectors();
    let mut failures = Vec::new();

    for vec in &vectors {
        let pk = hex_to_bytes(&vec.pk);
        let sig = hex_to_bytes(&vec.sig);

        // Generate witness using Rust implementation
        let rust_witness = serialize_witness(&pk, &sig);
        let rust_witness_hex = bytes_to_hex(&rust_witness);

        // Compare with expected (Coq/OCaml) output
        if rust_witness_hex != vec.witness {
            failures.push(format!(
                "Vector '{}' mismatch:\n  Expected (Coq): {}\n  Got (Rust):    {}",
                vec.name, vec.witness, rust_witness_hex
            ));
        }

        // Verify length consistency
        assert_eq!(
            pk.len(),
            vec.pk_len,
            "Vector '{}': pk_len mismatch",
            vec.name
        );
        assert_eq!(
            sig.len(),
            vec.sig_len,
            "Vector '{}': sig_len mismatch",
            vec.name
        );
    }

    if !failures.is_empty() {
        panic!(
            "PO-8 BOUNDED CORRESPONDENCE FAILED\n\
             ======================\n\
             The following vectors did not match the Coq-extracted serializer:\n\n\
             {}\n\n\
             PO-8: bounded correspondence evidence failed",
            failures.join("\n\n")
        );
    }

    println!(
        "PO-8 BOUNDED CORRESPONDENCE PASSED\n\
         =======================\n\
         {} bounded golden vectors verified byte-for-byte\n\
         Rust implementation matches Coq-extracted witness serialization\n\
         PO-8: bounded correspondence evidence holds",
        vectors.len()
    );
}

/// Test specific boundary cases for varint encoding
#[test]
fn po8_varint_boundary_cases() {
    // Test case 1: Exactly 252 bytes (largest single-byte varint)
    let pk_252 = vec![0xAAu8; 252];
    let sig_252 = vec![0xBBu8; 1];
    let w1 = serialize_witness(&pk_252, &sig_252);
    assert_eq!(w1[0], 252); // Single byte, no prefix
    assert_eq!(w1.len(), 1 + 252 + 1 + 1); // pk_len + pk + sig_len + sig

    // Test case 2: Exactly 253 bytes (smallest two-byte varint)
    let pk_253 = vec![0xCCu8; 253];
    let sig_253 = vec![0xDDu8; 1];
    let w2 = serialize_witness(&pk_253, &sig_253);
    assert_eq!(w2[0], 0xFD); // Two-byte prefix
    assert_eq!(w2[1], 253); // Little-endian low byte
    assert_eq!(w2[2], 0); // Little-endian high byte

    // Test case 3: Exactly 65535 bytes (largest two-byte varint)
    let pk_65535 = vec![0xEEu8; 65535];
    let sig_small = vec![0xFFu8; 1];
    let w3 = serialize_witness(&pk_65535, &sig_small);
    assert_eq!(w3[0], 0xFD);
    assert_eq!(w3[1], 0xFF); // 65535 = 0xFFFF
    assert_eq!(w3[2], 0xFF);

    // Test case 4: Exactly 65536 bytes (smallest four-byte varint)
    let pk_65536 = vec![0x11u8; 65536];
    let w4 = serialize_witness(&pk_65536, &sig_small);
    assert_eq!(w4[0], 0xFE); // Four-byte prefix
    assert_eq!(w4[1], 0x00); // 65536 = 0x00010000
    assert_eq!(w4[2], 0x00);
    assert_eq!(w4[3], 0x01);
    assert_eq!(w4[4], 0x00);
}

/// Test that parsing and re-serializing is identity (round-trip)
#[test]
fn po8_witness_round_trip_identity() {
    use pq_witness_protocol::encoding::parse_witness;

    // Generate random-ish test data
    let test_cases = vec![
        (vec![0x01], vec![0x02]),             // Single byte
        (vec![0xAB; 100], vec![0xCD; 50]),    // Small
        (vec![0xEF; 253], vec![0x12; 100]),   // Boundary 253
        (vec![0x34; 1000], vec![0x56; 2000]), // Medium
    ];

    for (pk, sig) in test_cases {
        let serialized = serialize_witness(&pk, &sig);
        let parsed = parse_witness(&serialized).expect("Parse should succeed");

        assert_eq!(parsed.0, pk, "Public key should round-trip exactly");
        assert_eq!(parsed.1, sig, "Signature should round-trip exactly");

        // Re-serializing should produce identical bytes
        let re_serialized = serialize_witness(&parsed.0, &parsed.1);
        assert_eq!(
            serialized, re_serialized,
            "Re-serialization should be canonical"
        );
    }
}

/// Test canonical encoding rejection (PO-3/PO-8 overlap)
#[test]
fn po8_non_canonical_encoding_rejection() {
    use pq_witness_protocol::encoding::decode_varint;

    // Non-canonical: 0xFD prefix for value < 253
    let non_canonical_1 = vec![0xFD, 0x01, 0x00]; // Value 1 with 0xFD prefix
    assert!(
        decode_varint(&non_canonical_1).is_none(),
        "Should reject non-canonical encoding (0xFD for value 1)"
    );

    // Non-canonical: 0xFE prefix for value < 65536
    let non_canonical_2 = vec![0xFE, 0x01, 0x00, 0x00, 0x00]; // Value 1 with 0xFE
    assert!(
        decode_varint(&non_canonical_2).is_none(),
        "Should reject non-canonical encoding (0xFE for small value)"
    );

    // Non-canonical: 0xFF prefix for value < 2^32
    let non_canonical_3 = vec![0xFF, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
    assert!(
        decode_varint(&non_canonical_3).is_none(),
        "Should reject non-canonical encoding (0xFF for small value)"
    );
}

/// Performance sanity check: ML-DSA-44 sized witness
#[test]
fn po8_ml_dsa_44_sized_witness() {
    // Real-world size: ML-DSA-44 pk = 1312 bytes, sig = 2420 bytes
    let pk = vec![0x42u8; 1312];
    let sig = vec![0x99u8; 2420];

    let witness = serialize_witness(&pk, &sig);

    // Check structure
    assert_eq!(witness[0], 0xFD); // 1312 requires 0xFD prefix
    assert_eq!(witness[1], 0x20); // 1312 = 0x0520 little-endian
    assert_eq!(witness[2], 0x05);

    let pk_end = 3 + 1312;
    assert_eq!(witness[pk_end], 0xFD); // 2420 requires 0xFD prefix
    assert_eq!(witness[pk_end + 1], 0x74); // 2420 = 0x0974 little-endian
    assert_eq!(witness[pk_end + 2], 0x09);

    let total_len = 3 + 1312 + 3 + 2420;
    assert_eq!(witness.len(), total_len);

    println!(
        "PO-8: ML-DSA-44 witness size = {} bytes (expected: {})",
        witness.len(),
        total_len
    );
}

/// Test SLH-DSA-128s sized witness
#[test]
fn po8_slh_dsa_128s_sized_witness() {
    // SLH-DSA-128s: pk = 32 bytes, sig = 7856 bytes
    let pk = vec![0x55u8; 32];
    let sig = vec![0x77u8; 7856];

    let witness = serialize_witness(&pk, &sig);

    // pk_len = 32 fits in single byte
    assert_eq!(witness[0], 32);

    // sig_len = 7856 requires 0xFD prefix
    let sig_len_pos = 1 + 32;
    assert_eq!(witness[sig_len_pos], 0xFD);
    assert_eq!(witness[sig_len_pos + 1], 0xB0); // 7856 = 0x1EB0 little-endian
    assert_eq!(witness[sig_len_pos + 2], 0x1E);

    let total_len = 1 + 32 + 3 + 7856;
    assert_eq!(witness.len(), total_len);

    println!(
        "PO-8: SLH-DSA-128s witness size = {} bytes (expected: {})",
        witness.len(),
        total_len
    );
}

/// Stress test: Very large witnesses (approaching MAX_WITNESS_SIZE)
#[test]
fn po8_large_witness_stress_test() {
    // Test with large but valid sizes
    let large_sizes = vec![
        (1000, 2000),
        (5000, 5000),
        (8000, 8000),
        (1312, 2420), // ML-DSA-44
        (32, 7856),   // SLH-DSA-128s
    ];

    for (pk_size, sig_size) in large_sizes {
        let pk = vec![0xABu8; pk_size];
        let sig = vec![0xCDu8; sig_size];

        let witness = serialize_witness(&pk, &sig);

        // Verify we can parse it back
        let parsed = parse_witness(&witness)
            .unwrap_or_else(|| panic!("Should parse witness of size {}", witness.len()));

        assert_eq!(parsed.0.len(), pk_size);
        assert_eq!(parsed.1.len(), sig_size);

        println!(
            "PO-8: Large witness (pk={}, sig={}) parsed successfully",
            pk_size, sig_size
        );
    }
}

/// Test the executable boundary between Rust's full CompactSize parser and the
/// consensus-valid witness subset covered by the current Coq model.
#[test]
fn po8_consensus_domain_guard_rejects_out_of_model_witnesses() {
    let max_domain = serialize_witness(&[0xAA], &vec![0xBB; MAX_WITNESS_SIZE - 5]);
    assert_eq!(max_domain.len(), MAX_WITNESS_SIZE);
    assert!(parse_witness(&max_domain).is_some());
    assert!(parse_consensus_witness(&max_domain).is_some());
    assert!(is_canonical_consensus_witness(&max_domain));

    let oversized = serialize_witness(&[0xAA], &vec![0xBB; MAX_WITNESS_SIZE - 4]);
    assert_eq!(oversized.len(), MAX_WITNESS_SIZE + 1);
    assert!(parse_witness(&oversized).is_some());
    assert_eq!(parse_consensus_witness(&oversized), None);
    assert!(!is_canonical_consensus_witness(&oversized));

    let full_compact_size = serialize_witness(&vec![0xCC; 65_536], &[0xDD]);
    assert_eq!(full_compact_size[0], 0xFE);
    assert!(parse_witness(&full_compact_size).is_some());
    assert_eq!(parse_consensus_witness(&full_compact_size), None);
    assert!(!is_canonical_consensus_witness(&full_compact_size));
}

/// Summary report for PO-8 verification
#[test]
fn po8_verification_summary() {
    println!("\n");
    println!("╔══════════════════════════════════════════════════════════════════╗");
    println!("║            PO-8 BOUNDED CORRESPONDENCE SUMMARY                    ║");
    println!("╠══════════════════════════════════════════════════════════════════╣");
    println!("║ Artifact: bounded implementation correspondence                   ║");
    println!("║ Method: golden vector comparison (Coq-extracted serializer ↔ Rust)║");
    println!("╠══════════════════════════════════════════════════════════════════╣");
    println!("║ Tests Executed:                                                  ║");
    println!("║   ✓ Byte-for-byte golden vector comparison                       ║");
    println!("║   ✓ Coq-domain varint boundaries (252, 253, 65535)              ║");
    println!("║   ✓ Rust-only full CompactSize boundary tests (65536+)          ║");
    println!("║   ✓ Consensus-domain parser keeps verified witnesses in u16     ║");
    println!("║   ✓ Oversized syntactic witnesses rejected outside PO-8 subset  ║");
    println!("║   ✓ Round-trip identity (parse ∘ serialize = id)              ║");
    println!("║   ✓ Non-canonical encoding rejection                             ║");
    println!("║   ✓ ML-DSA-44 sized witness validation                           ║");
    println!("║   ✓ SLH-DSA-128s sized witness validation                        ║");
    println!("║   ✓ Large witness stress tests                                     ║");
    println!("╠══════════════════════════════════════════════════════════════════╣");
    println!("║ Status: BOUNDED EVIDENCE                                           ║");
    println!("║                                                                    ║");
    println!("║ The Rust implementation produces byte-identical output             ║");
    println!("║ to the Coq-extracted serializer for the modeled u16 domain.       ║");
    println!("╚══════════════════════════════════════════════════════════════════╝");
}
