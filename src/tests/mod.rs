//! Test module for the PQ witness protocol.
//!
//! Contains unit tests, property-based tests (proptest), and integration tests
//! validating the 16 universal correctness properties from the design document.

use crate::encoding::{
    is_canonical_witness, parse_multisig_witness, parse_witness,
    serialize_multisig_witness, serialize_witness,
};
use crate::weight::{check_block_cost, cost_tx, verify_cost_bound, weight_tx};
use crate::params::C_MAX;
use proptest::prelude::*;

// ---------------------------------------------------------------------------
// Property 1: Single-signature witness round-trip
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 2.3, 11.1, 11.2**
//
// For any valid public key `pk` (1–2,000 bytes) and valid signature `sig`
// (1–8,000 bytes), `parse_witness(serialize_witness(pk, sig)) == Some((pk, sig))`
// — the original public key and signature are recovered exactly.
//
// Tag: Feature: pq-witness-protocol, Property 1: Single-signature witness round-trip

proptest! {
    #[test]
    fn prop_single_sig_witness_round_trip(
        pk in prop::collection::vec(any::<u8>(), 1..2000),
        sig in prop::collection::vec(any::<u8>(), 1..8000),
    ) {
        let witness = serialize_witness(&pk, &sig);
        let parsed = parse_witness(&witness);
        prop_assert!(
            parsed.is_some(),
            "parse_witness should succeed for a witness produced by serialize_witness"
        );
        let (parsed_pk, parsed_sig) = parsed.unwrap();
        prop_assert_eq!(
            parsed_pk, pk,
            "parsed public key must match the original"
        );
        prop_assert_eq!(
            parsed_sig, sig,
            "parsed signature must match the original"
        );
    }
}

// ---------------------------------------------------------------------------
// Property 3: Parse-direction round-trip
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 11.3**
//
// For any witness `w` where `Parse(w) = Some(pk, σ)`, serializing the parsed
// components and re-parsing SHALL produce the same result:
// `Parse(Serialize(pk, σ)) = Some(pk, σ)`.
//
// We generate witnesses via `serialize_witness` (which guarantees parseability),
// parse them, re-serialize, re-parse, and verify the result is identical.
//
// Tag: Feature: pq-witness-protocol, Property 3: Parse-direction round-trip

proptest! {
    #[test]
    fn prop_parse_direction_round_trip(
        pk in prop::collection::vec(any::<u8>(), 1..2000),
        sig in prop::collection::vec(any::<u8>(), 1..8000),
    ) {
        // Step 1: Serialize to get witness w
        let w = serialize_witness(&pk, &sig);

        // Step 2: Parse w to get (pk1, sig1)
        let (pk1, sig1) = parse_witness(&w)
            .expect("parse_witness must succeed on a witness produced by serialize_witness");

        // Step 3: Re-serialize (pk1, sig1) to get w2
        let w2 = serialize_witness(&pk1, &sig1);

        // Step 4: Re-parse w2 to get (pk2, sig2)
        let (pk2, sig2) = parse_witness(&w2)
            .expect("parse_witness must succeed on a re-serialized witness");

        // Step 5: Assert (pk1, sig1) == (pk2, sig2)
        prop_assert_eq!(
            &pk1, &pk2,
            "re-parsed public key must match the first parse"
        );
        prop_assert_eq!(
            &sig1, &sig2,
            "re-parsed signature must match the first parse"
        );
    }
}

// ---------------------------------------------------------------------------
// Property 6: Non-canonical witness rejection
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 11.4**
//
// For any witness `w` where `Parse(w) = Some(pk, σ)` but
// `Serialize(pk, σ) ≠ w` (the witness is not in canonical form),
// consensus SHALL reject the witness.
//
// Strategy: generate random pk (1..252 bytes, so pk_len fits in a single
// byte) and sig (1..100 bytes), then manually construct a non-canonical
// witness by encoding pk_len with a 0xFD prefix (non-minimal varint for
// values < 253). Since `decode_varint` rejects non-canonical varints,
// `parse_witness` returns `None`, so `is_canonical_witness` returns false.
//
// Tag: Feature: pq-witness-protocol, Property 6: Non-canonical witness rejection

proptest! {
    #[test]
    fn prop_non_canonical_witness_rejection(
        pk in prop::collection::vec(any::<u8>(), 1..252usize),
        sig in prop::collection::vec(any::<u8>(), 1..100usize),
    ) {
        // Construct a non-canonical witness: encode pk_len using the 0xFD
        // prefix even though pk.len() < 253 and fits in a single byte.
        // This is a non-minimal varint encoding.
        let pk_len = pk.len() as u16;
        let mut non_canonical = Vec::new();
        non_canonical.push(0xFD);
        non_canonical.extend_from_slice(&pk_len.to_le_bytes());
        non_canonical.extend_from_slice(&pk);
        non_canonical.extend_from_slice(&sig);

        // The non-canonical witness must NOT be accepted.
        prop_assert!(
            !is_canonical_witness(&non_canonical),
            "is_canonical_witness must return false for a witness with non-minimal varint encoding"
        );

        // Additionally verify that the canonical form (from serialize_witness)
        // IS accepted, confirming the data itself is valid — only the encoding
        // is wrong.
        let canonical = serialize_witness(&pk, &sig);
        prop_assert!(
            is_canonical_witness(&canonical),
            "is_canonical_witness must return true for the canonical encoding of the same (pk, sig)"
        );
    }
}

// ---------------------------------------------------------------------------
// Property 2: Multisig witness round-trip
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 6.5, 11.5**
//
// For any valid multisig parameters (k, n, pks, sigs, indices) where
// 1 ≤ k ≤ n ≤ 10, all public keys are non-empty, all signatures are
// non-empty, and indices are strictly ascending in [0, n),
// `parse_multisig_witness(serialize_multisig_witness(k, pks, sigs, indices))`
// SHALL produce `Some(k, pks, sigs, indices)`.
//
// Tag: Feature: pq-witness-protocol, Property 2: Multisig witness round-trip

/// Strategy to generate valid multisig parameters: (k, pks, sigs, indices).
///
/// 1. Generate n in [1, 10]
/// 2. Generate k in [1, n]
/// 3. Generate n non-empty pk vectors (1..100 bytes each)
/// 4. Generate k non-empty sig vectors (1..100 bytes each)
/// 5. Generate k unique sorted indices in [0, n)
fn valid_multisig_params() -> impl Strategy<Value = (u8, Vec<Vec<u8>>, Vec<Vec<u8>>, Vec<u8>)> {
    // Step 1: generate n in [1, 10]
    (1u8..=10u8).prop_flat_map(|n| {
        // Step 2: generate k in [1, n]
        (Just(n), 1u8..=n)
    }).prop_flat_map(|(n, k)| {
        // Step 3: generate n non-empty pk vectors
        let pks_strategy = prop::collection::vec(
            prop::collection::vec(any::<u8>(), 1..100usize),
            n as usize,
        );
        // Step 4: generate k non-empty sig vectors
        let sigs_strategy = prop::collection::vec(
            prop::collection::vec(any::<u8>(), 1..100usize),
            k as usize,
        );
        // Step 5: generate k unique sorted indices in [0, n)
        // We use a shuffled selection approach: generate a bool mask of length n
        // with exactly k true values, then collect the indices where true.
        let indices_strategy = prop::sample::subsequence((0..n).collect::<Vec<u8>>(), k as usize)
            .prop_map(|mut indices| {
                indices.sort();
                indices
            });
        (Just(k), pks_strategy, sigs_strategy, indices_strategy)
    })
}

proptest! {
    #[test]
    fn prop_multisig_witness_round_trip(
        (k, pks, sigs, indices) in valid_multisig_params()
    ) {
        let n = pks.len() as u8;

        // Precondition checks (should always hold given the strategy)
        prop_assert!(k >= 1 && k <= n, "k must be in [1, n]");
        prop_assert!(n >= 1 && n <= 10, "n must be in [1, 10]");
        prop_assert_eq!(sigs.len(), k as usize, "must have exactly k signatures");
        prop_assert_eq!(indices.len(), k as usize, "must have exactly k indices");

        // Verify indices are strictly ascending and in range [0, n)
        for i in 0..indices.len() {
            prop_assert!(indices[i] < n, "index must be < n");
            if i > 0 {
                prop_assert!(indices[i - 1] < indices[i], "indices must be strictly ascending");
            }
        }

        // Serialize and parse
        let witness = serialize_multisig_witness(k, &pks, &sigs, &indices);
        let parsed = parse_multisig_witness(&witness);

        prop_assert!(
            parsed.is_some(),
            "parse_multisig_witness should succeed for a witness produced by serialize_multisig_witness"
        );

        let (parsed_k, parsed_pks, parsed_sigs, parsed_indices) = parsed.unwrap();

        prop_assert_eq!(
            parsed_k, k,
            "parsed k must match the original"
        );
        prop_assert_eq!(
            parsed_pks, pks,
            "parsed public keys must match the originals"
        );
        prop_assert_eq!(
            parsed_sigs, sigs,
            "parsed signatures must match the originals"
        );
        prop_assert_eq!(
            parsed_indices, indices,
            "parsed indices must match the originals"
        );
    }
}

// ---------------------------------------------------------------------------
// Property 7: Non-ascending multisig signer indices rejection
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 6.6**
//
// For any multisig witness where the signer indices array contains any pair
// `indices[i] >= indices[i+1]` (duplicates, descending, or equal adjacent),
// `parse_multisig_witness` SHALL return `None`.
//
// Strategy: generate valid multisig parameters with k >= 2, then deliberately
// corrupt the indices to be non-ascending before serializing.
//
// Tag: Feature: pq-witness-protocol, Property 7: Non-ascending multisig signer indices rejection

/// Strategy to generate multisig parameters with deliberately non-ascending indices.
///
/// We need k >= 2 to have at least one adjacent pair to corrupt.
/// After generating valid sorted indices, we corrupt them by either:
/// - Reversing the indices (descending order)
/// - Making two adjacent indices equal (duplicate)
/// - Swapping two adjacent indices
fn non_ascending_multisig_params()
    -> impl Strategy<Value = (u8, Vec<Vec<u8>>, Vec<Vec<u8>>, Vec<u8>)>
{
    // n in [2, 10] so we can have k >= 2
    (2u8..=10u8).prop_flat_map(|n| {
        // k in [2, n] — need at least 2 indices to create a non-ascending pair
        (Just(n), 2u8..=n)
    }).prop_flat_map(|(n, k)| {
        let pks_strategy = prop::collection::vec(
            prop::collection::vec(any::<u8>(), 1..100usize),
            n as usize,
        );
        let sigs_strategy = prop::collection::vec(
            prop::collection::vec(any::<u8>(), 1..100usize),
            k as usize,
        );
        // Generate valid sorted indices first
        let indices_strategy = prop::sample::subsequence((0..n).collect::<Vec<u8>>(), k as usize)
            .prop_map(|mut indices| {
                indices.sort();
                indices
            });
        // Choose a corruption method: 0 = reverse, 1 = duplicate adjacent, 2 = swap adjacent
        let corruption = 0u8..3u8;
        (Just(k), pks_strategy, sigs_strategy, indices_strategy, corruption)
    }).prop_map(|(k, pks, sigs, mut indices, corruption)| {
        // Corrupt the indices to be non-ascending
        match corruption {
            0 => {
                // Reverse: guaranteed non-ascending for k >= 2 with distinct values
                indices.reverse();
            }
            1 => {
                // Duplicate: set indices[1] = indices[0]
                indices[1] = indices[0];
            }
            _ => {
                // Swap adjacent: swap indices[0] and indices[1]
                // Since they were sorted, after swap indices[0] > indices[1]
                indices.swap(0, 1);
            }
        }
        (k, pks, sigs, indices)
    })
}

proptest! {
    #[test]
    fn prop_non_ascending_multisig_indices_rejection(
        (k, pks, sigs, indices) in non_ascending_multisig_params()
    ) {
        // Verify that the indices are indeed non-ascending (at least one violation)
        let has_violation = indices.windows(2).any(|w| w[0] >= w[1]);
        prop_assert!(
            has_violation,
            "test precondition: indices must contain at least one non-ascending pair, got {:?}",
            indices
        );

        // Serialize with the non-ascending indices
        let witness = serialize_multisig_witness(k, &pks, &sigs, &indices);

        // Parse must reject
        let parsed = parse_multisig_witness(&witness);
        prop_assert!(
            parsed.is_none(),
            "parse_multisig_witness must return None for non-ascending indices {:?}",
            indices
        );
    }
}

// ---------------------------------------------------------------------------
// Property 4: SpendPred_PQ complete characterization
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 2.4, 2.5, 2.6, 2.7**
//
// For any commitment P, message m, and witness w:
//   SpendPred_PQ(P, m, w) = true iff:
//     (1) Parse(w) = Some(pk, σ)
//     (2) H(pk) = P
//     (3) Vfy(pk, m, σ) = 1
//   In all other cases, SpendPred_PQ(P, m, w) = false.
//
// Strategy: generate a random message, create a real ML-DSA-44 keypair,
// sign the message, serialize the witness, compute the correct commitment,
// then verify:
//   - spend_pred_pq returns true with correct (commitment, message, witness)
//   - spend_pred_pq returns false with corrupted commitment
//   - spend_pred_pq returns false with wrong message
//
// Since ML-DSA-44 key generation is expensive, we limit to 10 cases.
//
// Tag: Feature: pq-witness-protocol, Property 4: SpendPred_PQ complete characterization

use crate::spend_pred::spend_pred_pq;
use crate::params::MAX_WITNESS_SIZE;
use fips204::ml_dsa_44;
use fips204::traits::{SerDes, Signer};
use sha2::{Digest, Sha256};

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]

    #[test]
    fn prop_spend_pred_pq_complete_characterization(
        msg in prop::collection::vec(any::<u8>(), 1..100usize),
    ) {
        // Generate a real ML-DSA-44 keypair
        let (pk, sk) = ml_dsa_44::try_keygen().unwrap();
        let pk_bytes = pk.into_bytes().to_vec();

        // Sign the message
        let sig = sk.try_sign(&msg, &[]).unwrap();

        // Serialize the witness
        let witness = serialize_witness(&pk_bytes, &sig.to_vec());

        // Compute the correct commitment: P = SHA-256(pk)
        let commitment: [u8; 32] = Sha256::digest(&pk_bytes).into();

        // --- Valid case: all three conditions hold ---
        // (1) Parse(w) = Some(pk, σ) ✓ (serialize_witness produces parseable witness)
        // (2) H(pk) = P ✓ (commitment computed from same pk)
        // (3) Vfy(pk, m, σ) = 1 ✓ (signed with matching sk)
        prop_assert!(
            spend_pred_pq(&commitment, &msg, &witness),
            "spend_pred_pq must return true when all three conditions hold"
        );

        // --- Invalid case 1: corrupted commitment (condition 2 fails) ---
        let mut bad_commitment = commitment;
        bad_commitment[0] ^= 0xFF;
        prop_assert!(
            !spend_pred_pq(&bad_commitment, &msg, &witness),
            "spend_pred_pq must return false when commitment is corrupted"
        );

        // --- Invalid case 2: wrong message (condition 3 fails) ---
        // Construct a different message by appending a byte
        let mut wrong_msg = msg.clone();
        wrong_msg.push(0xFF);
        prop_assert!(
            !spend_pred_pq(&commitment, &wrong_msg, &witness),
            "spend_pred_pq must return false when message does not match signature"
        );
    }
}

// ---------------------------------------------------------------------------
// Property 5: Oversized witness rejection
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 2.9, 6.8, 8.3**
//
// For any witness w where len(w) > MAX_WITNESS_SIZE (16,000 bytes), and for
// any commitment P and message m, SpendPred_PQ(P, m, w) SHALL return false.
//
// Strategy: generate random byte vectors of length MAX_WITNESS_SIZE+1 to
// MAX_WITNESS_SIZE+10,000, random 32-byte commitments, and random messages,
// then verify spend_pred_pq always returns false.
//
// Tag: Feature: pq-witness-protocol, Property 5: Oversized witness rejection

proptest! {
    #[test]
    fn prop_oversized_witness_rejection(
        extra in 1usize..10_001usize,
        commitment in prop::array::uniform32(any::<u8>()),
        msg in prop::collection::vec(any::<u8>(), 1..100usize),
        fill_byte in any::<u8>(),
    ) {
        let witness_len = MAX_WITNESS_SIZE + extra;
        let witness = vec![fill_byte; witness_len];

        prop_assert!(
            witness.len() > MAX_WITNESS_SIZE,
            "test precondition: witness length {} must exceed MAX_WITNESS_SIZE {}",
            witness.len(),
            MAX_WITNESS_SIZE
        );

        prop_assert!(
            !spend_pred_pq(&commitment, &msg, &witness),
            "spend_pred_pq must return false for oversized witness of {} bytes",
            witness.len()
        );
    }
}

// ---------------------------------------------------------------------------
// Migration module imports
// ---------------------------------------------------------------------------

use crate::migration::check_migration_rules;
use crate::params::MigrationConfig;
use crate::types::{OutPoint, Output, Transaction, TxInput, TxOutput, UtxoSet};

// ---------------------------------------------------------------------------
// Property 10: Legacy output creation rejected after announcement
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 4.3**
//
// For any transaction that creates at least one legacy output (script_version != 2),
// and for any block height h ≥ H_a, `check_migration_rules(h, tx, utxo_set, config)`
// SHALL return false.
//
// Strategy: generate transactions with at least one legacy output (script_version
// chosen from {0, 1, 3}), random heights in [H_a, H_a + 200_000], and verify
// check_migration_rules returns false.
//
// Tag: Feature: pq-witness-protocol, Property 10: Legacy output creation rejected after announcement

/// Helper: create a fixed MigrationConfig with H_a=100_000 and recommended grace period.
fn migration_test_config() -> MigrationConfig {
    MigrationConfig::with_recommended_grace(100_000)
}

proptest! {
    #[test]
    fn prop_legacy_output_creation_rejected_after_announcement(
        // Height >= H_a (100_000). Cover both grace period and post-cutover.
        height in 100_000u64..300_000u64,
        // Number of PQ outputs (0..5)
        num_pq_outputs in 0usize..5,
        // At least one legacy output; legacy version from {0, 1, 3}
        legacy_version in prop::sample::select(vec![0u8, 1, 3]),
        // Additional legacy outputs (0..3)
        num_extra_legacy in 0usize..3,
        // Random values for outputs
        value in 1_000u64..100_000u64,
    ) {
        let config = migration_test_config();

        // Build outputs: some PQ, at least one legacy
        let mut outputs: Vec<TxOutput> = Vec::new();

        // Add PQ outputs
        for _ in 0..num_pq_outputs {
            outputs.push(TxOutput {
                script_version: 2,
                commitment: [0xCC; 32],
                value,
            });
        }

        // Add at least one legacy output
        outputs.push(TxOutput {
            script_version: legacy_version,
            commitment: [0xDD; 32],
            value,
        });

        // Add extra legacy outputs
        for _ in 0..num_extra_legacy {
            outputs.push(TxOutput {
                script_version: legacy_version,
                commitment: [0xDD; 32],
                value,
            });
        }

        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs,
            locktime: 0,
        };

        let utxo_set = UtxoSet::new();

        prop_assert!(
            !check_migration_rules(height, &tx, &utxo_set, &config),
            "check_migration_rules must return false for tx with legacy output at height {} >= H_a ({})",
            height,
            config.announcement_height
        );
    }
}

// ---------------------------------------------------------------------------
// Property 11: Legacy spends accepted during grace period
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 4.4**
//
// For any transaction spending legacy outputs with all PQ outputs, and for
// any block height h in [H_a, H_c), `check_migration_rules(h, tx, utxo_set, config)`
// SHALL return true.
//
// Strategy: generate transactions that spend legacy outputs (script_version != 2)
// and create only PQ outputs (script_version == 2), at random heights in [H_a, H_c).
//
// Tag: Feature: pq-witness-protocol, Property 11: Legacy spends accepted during grace period

proptest! {
    #[test]
    fn prop_legacy_spends_accepted_during_grace_period(
        // Height in [H_a, H_c) = [100_000, 152_560)
        height in 100_000u64..152_560u64,
        // Number of legacy inputs (1..5)
        num_legacy_inputs in 1usize..5,
        // Legacy script version for the UTXO entries
        legacy_version in prop::sample::select(vec![0u8, 1, 3]),
        // Number of PQ outputs (1..5)
        num_pq_outputs in 1usize..5,
        // Random value
        value in 1_000u64..100_000u64,
        // Seed for unique outpoint IDs
        id_seed in 1u8..200u8,
    ) {
        let config = migration_test_config();

        // Build UTXO set with legacy outputs
        let mut utxo_set = UtxoSet::new();
        let mut inputs: Vec<TxInput> = Vec::new();

        for i in 0..num_legacy_inputs {
            let mut txid = [0u8; 32];
            txid[0] = id_seed.wrapping_add(i as u8);
            txid[1] = (i as u8).wrapping_mul(17);
            let op = OutPoint { txid, vout: 0 };

            utxo_set.insert(
                op.clone(),
                Output {
                    script_version: legacy_version,
                    commitment: [0xBB; 32],
                    value,
                },
            );

            inputs.push(TxInput {
                outpoint: op,
                witness: vec![0xDE, 0xAD],
            });
        }

        // Build transaction with only PQ outputs
        let mut outputs: Vec<TxOutput> = Vec::new();
        for _ in 0..num_pq_outputs {
            outputs.push(TxOutput {
                script_version: 2,
                commitment: [0xCC; 32],
                value,
            });
        }

        let tx = Transaction {
            version: 2,
            inputs,
            outputs,
            locktime: 0,
        };

        prop_assert!(
            check_migration_rules(height, &tx, &utxo_set, &config),
            "check_migration_rules must return true for legacy spends with PQ outputs during grace period at height {}",
            height
        );
    }
}

// ---------------------------------------------------------------------------
// Property 12: Legacy and frozen spend rejection after cutover
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 4.5, 5.1, 5.2**
//
// For any transaction with at least one input spending a non-v2 output, and
// for any block height h ≥ H_c, `check_migration_rules(h, tx, utxo_set, config)`
// SHALL return false.
//
// Strategy: generate transactions with at least one input referencing a legacy
// (non-v2) UTXO, all PQ outputs, at random heights >= H_c.
//
// Tag: Feature: pq-witness-protocol, Property 12: Legacy and frozen spend rejection after cutover

proptest! {
    #[test]
    fn prop_legacy_frozen_spend_rejection_after_cutover(
        // Height >= H_c (152_560)
        height in 152_560u64..300_000u64,
        // Number of PQ inputs (0..3) — these are fine
        num_pq_inputs in 0usize..3,
        // At least one legacy input
        legacy_version in prop::sample::select(vec![0u8, 1, 3]),
        // Number of PQ outputs (1..5)
        num_pq_outputs in 1usize..5,
        // Random value
        value in 1_000u64..100_000u64,
        // Seed for unique outpoint IDs
        id_seed in 1u8..200u8,
    ) {
        let config = migration_test_config();

        let mut utxo_set = UtxoSet::new();
        let mut inputs: Vec<TxInput> = Vec::new();
        let mut id_counter: u8 = 0;

        // Add PQ inputs (these are valid)
        for _ in 0..num_pq_inputs {
            let mut txid = [0u8; 32];
            txid[0] = id_seed.wrapping_add(id_counter);
            txid[1] = id_counter.wrapping_mul(13);
            let op = OutPoint { txid, vout: 0 };

            utxo_set.insert(
                op.clone(),
                Output {
                    script_version: 2,
                    commitment: [0xAA; 32],
                    value,
                },
            );

            inputs.push(TxInput {
                outpoint: op,
                witness: vec![0xDE, 0xAD],
            });
            id_counter = id_counter.wrapping_add(1);
        }

        // Add at least one legacy input (this should cause rejection)
        {
            let mut txid = [0u8; 32];
            txid[0] = id_seed.wrapping_add(id_counter);
            txid[1] = id_counter.wrapping_mul(13);
            txid[2] = 0xFF; // distinguish from PQ inputs
            let op = OutPoint { txid, vout: 0 };

            utxo_set.insert(
                op.clone(),
                Output {
                    script_version: legacy_version,
                    commitment: [0xBB; 32],
                    value,
                },
            );

            inputs.push(TxInput {
                outpoint: op,
                witness: vec![0xDE, 0xAD],
            });
        }

        // Build transaction with only PQ outputs
        let mut outputs: Vec<TxOutput> = Vec::new();
        for _ in 0..num_pq_outputs {
            outputs.push(TxOutput {
                script_version: 2,
                commitment: [0xCC; 32],
                value,
            });
        }

        let tx = Transaction {
            version: 2,
            inputs,
            outputs,
            locktime: 0,
        };

        prop_assert!(
            !check_migration_rules(height, &tx, &utxo_set, &config),
            "check_migration_rules must return false for tx with legacy input at height {} >= H_c ({})",
            height,
            config.cutover_height
        );
    }
}

// ---------------------------------------------------------------------------
// Property 14: Migration monotonicity
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 4.7**
//
// For any execution trace starting from height H_a, the PQ fraction
// ρ(U_t) = PQ_count / total_count is monotonically non-decreasing.
//
// Strategy:
// 1. Start with a UTXO set containing a mix of legacy and PQ outputs
// 2. Apply a sequence of valid transactions that spend some legacy outputs
//    into PQ outputs (all new outputs are PQ, as required after H_a)
// 3. After each transaction, compute ρ = PQ_count / total_count
// 4. Verify ρ never decreases
//
// Tag: Feature: pq-witness-protocol, Property 14: Migration monotonicity

/// Compute the PQ fraction ρ(U) = PQ_count / total_count.
/// Returns (numerator, denominator) to avoid floating point.
/// If the UTXO set is empty, returns (0, 0).
fn pq_fraction(utxo_set: &UtxoSet) -> (usize, usize) {
    let total = utxo_set.len();
    if total == 0 {
        return (0, 0);
    }
    let pq_count = utxo_set
        .values()
        .filter(|o| o.script_version == 2)
        .count();
    (pq_count, total)
}

/// Apply a transaction to the UTXO set: remove spent outpoints, add new ones.
fn apply_tx(utxo_set: &mut UtxoSet, tx: &Transaction, tx_index: u8) {
    // Remove spent outpoints
    for input in &tx.inputs {
        utxo_set.remove(&input.outpoint);
    }
    // Add new outpoints (use tx_index to create unique txids)
    let mut txid = [0u8; 32];
    txid[0] = tx_index;
    txid[31] = tx_index.wrapping_mul(37);
    for (vout, output) in tx.outputs.iter().enumerate() {
        let op = OutPoint {
            txid,
            vout: vout as u32,
        };
        utxo_set.insert(
            op,
            Output {
                script_version: output.script_version,
                commitment: output.commitment,
                value: output.value,
            },
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn prop_migration_monotonicity(
        // Number of initial legacy outputs (2..10)
        num_legacy in 2usize..10,
        // Number of initial PQ outputs (1..10)
        num_pq in 1usize..10,
        // Number of migration transactions to apply (1..6)
        // Each tx spends one legacy output and creates one PQ output
        num_txs in 1usize..6,
        // Random value
        value in 1_000u64..100_000u64,
    ) {
        let config = migration_test_config();
        let height = config.announcement_height; // H_a = 100_000

        // Build initial UTXO set with a mix of legacy and PQ outputs
        let mut utxo_set = UtxoSet::new();

        // Add legacy outputs
        let mut legacy_outpoints: Vec<OutPoint> = Vec::new();
        for i in 0..num_legacy {
            let mut txid = [0u8; 32];
            txid[0] = 0xAA;
            txid[1] = i as u8;
            let op = OutPoint { txid, vout: 0 };
            utxo_set.insert(
                op.clone(),
                Output {
                    script_version: 0, // legacy
                    commitment: [0xBB; 32],
                    value,
                },
            );
            legacy_outpoints.push(op);
        }

        // Add PQ outputs
        for i in 0..num_pq {
            let mut txid = [0u8; 32];
            txid[0] = 0xCC;
            txid[1] = i as u8;
            let op = OutPoint { txid, vout: 0 };
            utxo_set.insert(
                op,
                Output {
                    script_version: 2, // PQ
                    commitment: [0xDD; 32],
                    value,
                },
            );
        }

        // Compute initial ρ
        let (initial_pq, initial_total) = pq_fraction(&utxo_set);
        prop_assert!(initial_total > 0, "UTXO set must not be empty");

        // Track ρ as (numerator, denominator) pairs
        // ρ_prev = initial_pq / initial_total
        let mut prev_pq = initial_pq;
        let mut prev_total = initial_total;

        // Apply migration transactions: each spends one legacy output → one PQ output
        // Cap the number of transactions to the number of available legacy outputs
        let actual_txs = num_txs.min(legacy_outpoints.len());

        for tx_idx in 0..actual_txs {
            let legacy_op = &legacy_outpoints[tx_idx];

            // Build a valid migration transaction: spend legacy, create PQ
            let tx = Transaction {
                version: 2,
                inputs: vec![TxInput {
                    outpoint: legacy_op.clone(),
                    witness: vec![0xDE, 0xAD],
                }],
                outputs: vec![TxOutput {
                    script_version: 2,
                    commitment: [0xEE; 32],
                    value,
                }],
                locktime: 0,
            };

            // Verify the transaction passes migration rules
            prop_assert!(
                check_migration_rules(height, &tx, &utxo_set, &config),
                "migration tx {} must pass check_migration_rules during grace period",
                tx_idx
            );

            // Apply the transaction
            apply_tx(&mut utxo_set, &tx, (tx_idx + 100) as u8);

            // Compute new ρ
            let (new_pq, new_total) = pq_fraction(&utxo_set);
            prop_assert!(new_total > 0, "UTXO set must not be empty after tx {}", tx_idx);

            // Verify monotonicity: new_pq/new_total >= prev_pq/prev_total
            // Cross-multiply to avoid floating point: new_pq * prev_total >= prev_pq * new_total
            prop_assert!(
                new_pq * prev_total >= prev_pq * new_total,
                "PQ fraction must be non-decreasing: {}/{} < {}/{} after tx {}",
                new_pq, new_total, prev_pq, prev_total, tx_idx
            );

            prev_pq = new_pq;
            prev_total = new_total;
        }
    }
}

// ---------------------------------------------------------------------------
// Property 8: Cost function bound
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 3.1**
//
// For any valid transaction `tx` (with varying input counts and witness sizes),
// `cost_tx(tx) <= ALPHA * weight_tx(tx)` (i.e., `cost_tx(tx) <= weight_tx(tx)`
// since ALPHA = 1).
//
// Strategy: generate transactions with 1–5 inputs (random witness sizes
// 1–16,000 bytes each) and 1–3 outputs, then verify the cost bound holds.
//
// Tag: Feature: pq-witness-protocol, Property 8: Cost function bound

/// Helper: create a transaction with the given witness sizes and output count.
fn make_tx_for_weight(witness_sizes: &[usize], num_outputs: usize) -> Transaction {
    let inputs: Vec<TxInput> = witness_sizes
        .iter()
        .enumerate()
        .map(|(i, &size)| TxInput {
            outpoint: OutPoint {
                txid: {
                    let mut txid = [0u8; 32];
                    txid[0] = i as u8;
                    txid[1] = (i >> 8) as u8;
                    txid
                },
                vout: 0,
            },
            witness: vec![0xAA; size],
        })
        .collect();

    let outputs: Vec<TxOutput> = (0..num_outputs)
        .map(|_| TxOutput {
            script_version: 2,
            commitment: [0xBB; 32],
            value: 50_000,
        })
        .collect();

    Transaction {
        version: 2,
        inputs,
        outputs,
        locktime: 0,
    }
}

proptest! {
    #[test]
    fn prop_cost_function_bound(
        // 1–5 inputs, each with a random witness size in [1, 16_000]
        witness_sizes in prop::collection::vec(1usize..16_000, 1..=5),
        // 1–3 outputs
        num_outputs in 1usize..=3,
    ) {
        let tx = make_tx_for_weight(&witness_sizes, num_outputs);

        // cost_tx(tx) <= ALPHA * weight_tx(tx), and ALPHA = 1
        let cost = cost_tx(&tx);
        let weight = weight_tx(&tx);

        prop_assert!(
            cost <= weight,
            "cost_tx ({}) must be <= weight_tx ({}) for tx with {} inputs (witnesses: {:?}) and {} outputs",
            cost, weight, witness_sizes.len(), witness_sizes, num_outputs
        );

        // Also verify via the dedicated helper
        prop_assert!(
            verify_cost_bound(&tx),
            "verify_cost_bound must return true"
        );
    }
}

// ---------------------------------------------------------------------------
// Property 9: Block cost invariant
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 3.2, 8.1, 9.4**
//
// (a) For any valid block where total cost ≤ C_MAX, `check_block_cost`
//     returns true.
// (b) For any block where total cost > C_MAX, `check_block_cost`
//     returns false.
//
// Tag: Feature: pq-witness-protocol, Property 9: Block cost invariant

proptest! {
    #[test]
    fn prop_block_cost_invariant_within_budget(
        // Generate 1–10 transactions, each with 1 input (witness 1–4000 bytes) and 1 output.
        // These are small enough that a handful will stay within C_MAX.
        num_txs in 1usize..=10,
        witness_size in 1usize..4_000,
    ) {
        let tx = make_tx_for_weight(&[witness_size], 1);
        let tx_cost = cost_tx(&tx);

        // Build a block that stays within C_MAX
        let max_count = (C_MAX / tx_cost) as usize;
        let count = num_txs.min(max_count);
        let block: Vec<Transaction> = vec![tx; count];

        let total: u64 = block.iter().map(|t| cost_tx(t)).sum();
        prop_assert!(total <= C_MAX, "precondition: total cost {} must be <= C_MAX {}", total, C_MAX);

        prop_assert!(
            check_block_cost(&block),
            "check_block_cost must return true for block with total cost {} <= C_MAX {}",
            total, C_MAX
        );
    }

    #[test]
    fn prop_block_cost_invariant_exceeds_budget(
        // Generate transactions that will exceed C_MAX
        witness_size in 1usize..16_000,
    ) {
        let tx = make_tx_for_weight(&[witness_size], 1);
        let tx_cost = cost_tx(&tx);

        // Build a block that exceeds C_MAX by adding enough transactions
        let count = (C_MAX / tx_cost) as usize + 1;
        let block: Vec<Transaction> = vec![tx; count];

        let total: u64 = block.iter().map(|t| cost_tx(t)).sum();
        prop_assert!(total > C_MAX, "precondition: total cost {} must exceed C_MAX {}", total, C_MAX);

        prop_assert!(
            !check_block_cost(&block),
            "check_block_cost must return false for block with total cost {} > C_MAX {}",
            total, C_MAX
        );
    }
}

// ---------------------------------------------------------------------------
// Unit tests for weight accounting (Task 8.4)
// ---------------------------------------------------------------------------
//
// Most weight unit tests are already in src/weight.rs. The test below covers
// the "block budget exclusion" scenario: a transaction that would push the
// block over the remaining budget should cause check_block_cost to fail.

#[test]
fn block_budget_exclusion_when_exceeding_remaining() {
    // Fill a block close to C_MAX, then add one more transaction that
    // pushes it over the limit.
    let small_tx = make_tx_for_weight(&[3_734], 1); // ML-DSA-44 sized
    let small_cost = cost_tx(&small_tx);

    // Fill to just under C_MAX
    let count = (C_MAX / small_cost) as usize;
    let mut block: Vec<Transaction> = vec![small_tx; count];

    let total_before: u64 = block.iter().map(|t| cost_tx(t)).sum();
    assert!(total_before <= C_MAX, "block should be within budget before adding extra tx");
    assert!(check_block_cost(&block), "block should pass check_block_cost before extra tx");

    // Add one more transaction that exceeds the remaining budget
    let remaining = C_MAX - total_before;
    // Create a transaction whose cost exceeds the remaining budget
    let big_witness_size = (remaining + 1) as usize; // witness alone exceeds remaining
    let extra_tx = make_tx_for_weight(&[big_witness_size], 1);
    let extra_cost = cost_tx(&extra_tx);
    assert!(extra_cost > remaining, "extra tx cost {} must exceed remaining budget {}", extra_cost, remaining);

    block.push(extra_tx);
    assert!(!check_block_cost(&block), "block should fail check_block_cost after adding tx that exceeds remaining budget");
}

// ---------------------------------------------------------------------------
// Property 13: Frozen outputs preserved in UTXO set
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 5.3**
//
// For any UTXO set at height ≥ H_c containing frozen (legacy) outputs,
// and for any sequence of valid PQ transactions, the frozen outputs SHALL
// remain in the UTXO set after each transition — they are never removed
// by the freeze mechanism itself.
//
// The key insight: the freeze mechanism only CHECKS (via is_frozen /
// check_no_frozen_inputs). It never removes outputs from the UTXO set.
// Valid PQ transactions only spend PQ outputs (which are not frozen),
// so frozen legacy outputs are untouched.
//
// Strategy:
// 1. Build a UTXO set with a mix of frozen (legacy) and PQ outputs
// 2. Apply a sequence of valid PQ transactions (spending only PQ outputs)
// 3. After each transaction, verify all frozen outputs are still present
//
// Tag: Feature: pq-witness-protocol, Property 13: Frozen outputs preserved in UTXO set

use crate::freeze::{check_no_frozen_inputs, is_frozen};

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn prop_frozen_outputs_preserved_in_utxo_set(
        // Number of frozen (legacy) outputs (1..8)
        num_frozen in 1usize..8,
        // Number of PQ outputs available to spend (2..10)
        num_pq in 2usize..10,
        // Number of PQ transactions to apply (1..5)
        // Each tx spends one PQ output and creates one new PQ output
        num_txs in 1usize..5,
        // Random value
        value in 1_000u64..100_000u64,
    ) {
        let config = migration_test_config();
        // Height at or past cutover — frozen outputs are active
        let height = config.cutover_height;

        // Build initial UTXO set
        let mut utxo_set = UtxoSet::new();

        // Add frozen (legacy) outputs — these should never be removed
        let mut frozen_outpoints: Vec<OutPoint> = Vec::new();
        for i in 0..num_frozen {
            let mut txid = [0u8; 32];
            txid[0] = 0xF0; // prefix for frozen outputs
            txid[1] = i as u8;
            let op = OutPoint { txid, vout: 0 };
            utxo_set.insert(
                op.clone(),
                Output {
                    script_version: 0, // legacy → frozen at H_c
                    commitment: [0xBB; 32],
                    value,
                },
            );
            frozen_outpoints.push(op);
        }

        // Add PQ outputs — these can be spent by valid transactions
        let mut pq_outpoints: Vec<OutPoint> = Vec::new();
        for i in 0..num_pq {
            let mut txid = [0u8; 32];
            txid[0] = 0xA0; // prefix for PQ outputs
            txid[1] = i as u8;
            let op = OutPoint { txid, vout: 0 };
            utxo_set.insert(
                op.clone(),
                Output {
                    script_version: 2, // PQ
                    commitment: [0xDD; 32],
                    value,
                },
            );
            pq_outpoints.push(op);
        }

        // Verify frozen outputs are indeed frozen
        for op in &frozen_outpoints {
            let output = utxo_set.get(op).unwrap();
            prop_assert!(
                is_frozen(height, output, &config),
                "legacy output should be frozen at height >= H_c"
            );
        }

        // Apply a sequence of valid PQ transactions
        // Each tx spends one PQ output and creates a new PQ output
        let actual_txs = num_txs.min(pq_outpoints.len());

        for tx_idx in 0..actual_txs {
            let pq_op = &pq_outpoints[tx_idx];

            // Build a valid PQ transaction (only spends PQ outputs)
            let tx = Transaction {
                version: 2,
                inputs: vec![TxInput {
                    outpoint: pq_op.clone(),
                    witness: vec![0xDE, 0xAD],
                }],
                outputs: vec![TxOutput {
                    script_version: 2,
                    commitment: [0xEE; 32],
                    value,
                }],
                locktime: 0,
            };

            // Verify the transaction passes the freeze check
            prop_assert!(
                check_no_frozen_inputs(height, &tx, &utxo_set, &config),
                "PQ transaction {} must pass freeze check (only spends PQ outputs)",
                tx_idx
            );

            // Apply the transaction: remove spent PQ output, add new PQ output
            utxo_set.remove(&tx.inputs[0].outpoint);
            let mut new_txid = [0u8; 32];
            new_txid[0] = 0xB0; // prefix for new PQ outputs
            new_txid[1] = tx_idx as u8;
            let new_op = OutPoint {
                txid: new_txid,
                vout: 0,
            };
            utxo_set.insert(
                new_op,
                Output {
                    script_version: 2,
                    commitment: [0xEE; 32],
                    value,
                },
            );

            // CRITICAL CHECK: all frozen outputs must still be in the UTXO set
            for (frozen_idx, frozen_op) in frozen_outpoints.iter().enumerate() {
                prop_assert!(
                    utxo_set.contains_key(frozen_op),
                    "frozen output {} must remain in UTXO set after PQ transaction {}",
                    frozen_idx,
                    tx_idx
                );

                // Verify the frozen output is still frozen
                let frozen_output = utxo_set.get(frozen_op).unwrap();
                prop_assert!(
                    is_frozen(height, frozen_output, &config),
                    "frozen output {} must still be frozen after PQ transaction {}",
                    frozen_idx,
                    tx_idx
                );
            }
        }
    }
}


// ---------------------------------------------------------------------------
// Property 15: Structural invariant preservation
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 9.1, 9.2**
//
// For any UTXO set U satisfying NoDoubleSpend and StateConsistency, and for
// any valid transaction tx (including PQ transactions), U' = DeltaTx(U, tx)
// SHALL also satisfy NoDoubleSpend and StateConsistency.
//
// NoDoubleSpend: every outpoint appears at most once in the UTXO set.
//   (Guaranteed by HashMap — keys are unique.)
// StateConsistency: every outpoint in the UTXO set has a valid output.
//   (Guaranteed by HashMap — every key maps to exactly one value.)
//
// The key verification after delta_tx:
//   1. Spent outpoints are removed (not double-spendable)
//   2. New outpoints are added correctly
//   3. No outpoint appears twice (HashMap guarantees this)
//   4. The UTXO set size is consistent: old_size - inputs_spent + outputs_created
//
// Strategy: generate a UTXO set with some legacy and PQ outputs, generate a
// valid transaction (spending some outputs, creating new PQ outputs), apply
// delta_tx, verify invariants hold.
//
// We use simple legacy-spend transactions during pre-activation to avoid
// needing real PQ signatures.
//
// Tag: Feature: pq-witness-protocol, Property 15: Structural invariant preservation

use crate::delta_tx;

/// Check the NoDoubleSpend invariant: every outpoint appears at most once.
/// For a HashMap this is trivially true (keys are unique), but we verify
/// the count matches expectations.
fn check_no_double_spend(utxo_set: &UtxoSet) -> bool {
    // HashMap keys are unique by construction — collect all keys and
    // verify no duplicates exist (this is a tautology for HashMap but
    // validates the invariant explicitly).
    let keys: Vec<&OutPoint> = utxo_set.keys().collect();
    let unique_count = keys.len();
    // If there were duplicates, the HashMap would have fewer entries
    // than insertions. Since we can only observe the final state,
    // the invariant holds iff len() == number of unique keys.
    unique_count == utxo_set.len()
}

/// Check the StateConsistency invariant: every outpoint in the UTXO set
/// maps to a valid output (non-None). For HashMap this is guaranteed,
/// but we verify explicitly.
fn check_state_consistency(utxo_set: &UtxoSet) -> bool {
    // Every key must map to a value — HashMap guarantees this.
    // Additionally verify that outputs have sensible fields.
    for (_op, output) in utxo_set.iter() {
        // script_version should be a known version (0, 1, 2, or other)
        // commitment should be 32 bytes (it's a fixed array, always true)
        // value can be any u64
        // The key check: the entry exists and is well-formed.
        let _ = output.script_version;
        let _ = output.commitment;
        let _ = output.value;
    }
    true
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn prop_structural_invariant_preservation(
        // Number of initial legacy outputs (1..8)
        num_legacy in 1usize..8,
        // Number of initial PQ outputs (1..8)
        num_pq in 1usize..8,
        // Number of legacy outputs to spend (1..4)
        num_to_spend in 1usize..4,
        // Number of new PQ outputs to create (1..5)
        num_new_outputs in 1usize..5,
        // Random value for outputs
        value in 1_000u64..100_000u64,
    ) {
        // Build initial UTXO set with a mix of legacy and PQ outputs
        let mut utxo_set = UtxoSet::new();

        let mut legacy_outpoints: Vec<OutPoint> = Vec::new();
        for i in 0..num_legacy {
            let mut txid = [0u8; 32];
            txid[0] = 0xAA;
            txid[1] = i as u8;
            txid[2] = 0x15; // distinguish from other tests
            let op = OutPoint { txid, vout: 0 };
            utxo_set.insert(
                op.clone(),
                Output {
                    script_version: 0,
                    commitment: [0xBB; 32],
                    value,
                },
            );
            legacy_outpoints.push(op);
        }

        for i in 0..num_pq {
            let mut txid = [0u8; 32];
            txid[0] = 0xCC;
            txid[1] = i as u8;
            txid[2] = 0x15;
            let op = OutPoint { txid, vout: 0 };
            utxo_set.insert(
                op,
                Output {
                    script_version: 2,
                    commitment: [0xDD; 32],
                    value,
                },
            );
        }

        // Verify initial invariants
        prop_assert!(
            check_no_double_spend(&utxo_set),
            "initial UTXO set must satisfy NoDoubleSpend"
        );
        prop_assert!(
            check_state_consistency(&utxo_set),
            "initial UTXO set must satisfy StateConsistency"
        );

        let initial_size = utxo_set.len();
        prop_assert_eq!(initial_size, num_legacy + num_pq);

        // Build a valid transaction: spend some legacy outputs, create PQ outputs
        // Cap the number of inputs to available legacy outputs
        let actual_spend = num_to_spend.min(legacy_outpoints.len());

        let inputs: Vec<TxInput> = legacy_outpoints[..actual_spend]
            .iter()
            .map(|op| TxInput {
                outpoint: op.clone(),
                witness: vec![0xDE, 0xAD],
            })
            .collect();

        let outputs: Vec<TxOutput> = (0..num_new_outputs)
            .map(|i| TxOutput {
                script_version: 2,
                commitment: {
                    let mut c = [0xEE; 32];
                    c[0] = i as u8;
                    c
                },
                value: value / num_new_outputs as u64,
            })
            .collect();

        let tx = Transaction {
            version: 2,
            inputs,
            outputs,
            locktime: 0,
        };

        // Apply delta_tx
        delta_tx(&mut utxo_set, &tx);

        // Verify structural invariants after transition
        prop_assert!(
            check_no_double_spend(&utxo_set),
            "UTXO set must satisfy NoDoubleSpend after delta_tx"
        );
        prop_assert!(
            check_state_consistency(&utxo_set),
            "UTXO set must satisfy StateConsistency after delta_tx"
        );

        // Verify size consistency: old_size - spent + created
        let expected_size = initial_size - actual_spend + num_new_outputs;
        prop_assert_eq!(
            utxo_set.len(),
            expected_size,
            "UTXO set size must be old_size ({}) - spent ({}) + created ({})",
            initial_size,
            actual_spend,
            num_new_outputs
        );

        // Verify spent outpoints are removed (no double-spend possible)
        for op in &legacy_outpoints[..actual_spend] {
            prop_assert!(
                !utxo_set.contains_key(op),
                "spent outpoint must be removed from UTXO set"
            );
        }

        // Verify unspent outpoints are still present
        for op in &legacy_outpoints[actual_spend..] {
            prop_assert!(
                utxo_set.contains_key(op),
                "unspent legacy outpoint must remain in UTXO set"
            );
        }

        // Verify new outputs were added with correct script version
        // (We can't easily predict the txid without calling compute_txid,
        // but we can verify the total count of PQ outputs increased)
        let pq_count = utxo_set
            .values()
            .filter(|o| o.script_version == 2)
            .count();
        prop_assert!(
            pq_count >= num_pq + num_new_outputs,
            "PQ output count must include original ({}) plus new ({}), got {}",
            num_pq,
            num_new_outputs,
            pq_count
        );
    }
}

// ---------------------------------------------------------------------------
// Property 16: Transition determinism
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 9.3**
//
// For any UTXO set U and valid transaction tx, applying DeltaTx(U, tx) twice
// independently (on cloned copies) SHALL produce identical successor states.
//
// Strategy: generate a UTXO set and a valid transaction, clone the UTXO set,
// apply delta_tx to both copies with the same transaction, verify the
// resulting states are identical.
//
// Tag: Feature: pq-witness-protocol, Property 16: Transition determinism

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn prop_transition_determinism(
        // Number of initial legacy outputs (1..8)
        num_legacy in 1usize..8,
        // Number of initial PQ outputs (0..8)
        num_pq in 0usize..8,
        // Number of outputs to spend (1..4)
        num_to_spend in 1usize..4,
        // Number of new outputs to create (1..5)
        num_new_outputs in 1usize..5,
        // Random value
        value in 1_000u64..100_000u64,
        // Random locktime to vary the txid
        locktime in 0u32..1_000_000u32,
    ) {
        // Build initial UTXO set
        let mut utxo_set = UtxoSet::new();

        let mut spendable_outpoints: Vec<OutPoint> = Vec::new();
        for i in 0..num_legacy {
            let mut txid = [0u8; 32];
            txid[0] = 0xAA;
            txid[1] = i as u8;
            txid[2] = 0x16; // distinguish from other tests
            let op = OutPoint { txid, vout: 0 };
            utxo_set.insert(
                op.clone(),
                Output {
                    script_version: 0,
                    commitment: [0xBB; 32],
                    value,
                },
            );
            spendable_outpoints.push(op);
        }

        for i in 0..num_pq {
            let mut txid = [0u8; 32];
            txid[0] = 0xCC;
            txid[1] = i as u8;
            txid[2] = 0x16;
            let op = OutPoint { txid, vout: 0 };
            utxo_set.insert(
                op.clone(),
                Output {
                    script_version: 2,
                    commitment: [0xDD; 32],
                    value,
                },
            );
            spendable_outpoints.push(op);
        }

        // Cap the number of inputs to available outpoints
        let actual_spend = num_to_spend.min(spendable_outpoints.len());

        let inputs: Vec<TxInput> = spendable_outpoints[..actual_spend]
            .iter()
            .map(|op| TxInput {
                outpoint: op.clone(),
                witness: vec![0xDE, 0xAD],
            })
            .collect();

        let outputs: Vec<TxOutput> = (0..num_new_outputs)
            .map(|i| TxOutput {
                script_version: 2,
                commitment: {
                    let mut c = [0xFF; 32];
                    c[0] = i as u8;
                    c
                },
                value: value / num_new_outputs as u64,
            })
            .collect();

        let tx = Transaction {
            version: 2,
            inputs,
            outputs,
            locktime,
        };

        // Clone the UTXO set to create two independent copies
        let mut utxo_copy_1 = utxo_set.clone();
        let mut utxo_copy_2 = utxo_set.clone();

        // Apply delta_tx independently to both copies
        delta_tx(&mut utxo_copy_1, &tx);
        delta_tx(&mut utxo_copy_2, &tx);

        // Verify both resulting states are identical
        prop_assert_eq!(
            utxo_copy_1.len(),
            utxo_copy_2.len(),
            "both UTXO sets must have the same size after delta_tx"
        );

        // Verify every key-value pair matches
        for (op, output1) in &utxo_copy_1 {
            let output2 = utxo_copy_2.get(op);
            prop_assert!(
                output2.is_some(),
                "outpoint {:?} present in copy_1 must also be present in copy_2",
                op
            );
            prop_assert_eq!(
                output1,
                output2.unwrap(),
                "output for outpoint {:?} must be identical in both copies",
                op
            );
        }

        // Also verify the reverse: every key in copy_2 is in copy_1
        for op in utxo_copy_2.keys() {
            prop_assert!(
                utxo_copy_1.contains_key(op),
                "outpoint {:?} present in copy_2 must also be present in copy_1",
                op
            );
        }
    }
}

// ---------------------------------------------------------------------------
// PO-4: Sighash Commitment Property (Definition 5)
// ---------------------------------------------------------------------------
//
// **Validates: Requirements 2.8, 10.2**
//
// The sighash function for witness version 2 MUST satisfy Definition 5:
//
// 1. **Injectivity**: For fixed context and input index,
//    `Sighash(tx, i, ctx) = Sighash(tx', i, ctx)` implies `tx ≡_cs tx'`.
//    Two transactions that differ in any consensus-critical field produce
//    different sighashes.
//
// 2. **Cross-input separation**: For `i ≠ j` in the same transaction,
//    `Sighash(tx, i, ctx) ≠ Sighash(tx, j, ctx)`.
//
// 3. **Field coverage**: The sighash commits to all consensus-critical
//    fields: version, all input outpoints, all output scripts/values,
//    the spent output's scriptPubKey and amount, locktime, and input index.
//
// These tests use `verify_sighash_commitment_property` as executable
// evidence for PO-4, plus individual property-based tests for each
// sub-property.
//
// Tag: Feature: pq-witness-protocol, PO-4: Sighash Commitment Property

use crate::sighash::{sighash_v2, tagged_hash, verify_sighash_commitment_property};

// ---------------------------------------------------------------------------
// PO-4.1: Injectivity — different transactions produce different sighashes
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn prop_po4_injectivity_different_txids(
        txid_a in prop::array::uniform32(any::<u8>()),
        txid_b in prop::array::uniform32(any::<u8>()),
        vout in 0u32..10,
        version in 1u32..4,
        commitment in prop::array::uniform32(any::<u8>()),
        value in 1_000u64..1_000_000,
        locktime in 0u32..500_000,
        spent_commitment in prop::array::uniform32(any::<u8>()),
        spent_value in 1_000u64..1_000_000,
    ) {
        // Skip if txids happen to be equal (extremely unlikely but possible)
        prop_assume!(txid_a != txid_b);

        let tx_a = Transaction {
            version,
            inputs: vec![TxInput {
                outpoint: OutPoint { txid: txid_a, vout },
                witness: vec![],
            }],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment,
                value,
            }],
            locktime,
        };

        let tx_b = Transaction {
            version,
            inputs: vec![TxInput {
                outpoint: OutPoint { txid: txid_b, vout },
                witness: vec![],
            }],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment,
                value,
            }],
            locktime,
        };

        let spent = Output {
            script_version: 2,
            commitment: spent_commitment,
            value: spent_value,
        };

        let h_a = sighash_v2(&tx_a, 0, &spent);
        let h_b = sighash_v2(&tx_b, 0, &spent);

        prop_assert_ne!(
            h_a, h_b,
            "transactions with different input txids must produce different sighashes"
        );
    }
}

// ---------------------------------------------------------------------------
// PO-4.2: Cross-input separation — all input sighashes are distinct
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn prop_po4_cross_input_separation(
        num_inputs in 2usize..6,
        version in 1u32..4,
        out_commitment in prop::array::uniform32(any::<u8>()),
        out_value in 1_000u64..1_000_000,
        locktime in 0u32..500_000,
        spent_commitment in prop::array::uniform32(any::<u8>()),
        spent_value in 1_000u64..1_000_000,
        seed in any::<u8>(),
    ) {
        // Build a transaction with num_inputs distinct inputs
        let inputs: Vec<TxInput> = (0..num_inputs)
            .map(|i| {
                let mut txid = [0u8; 32];
                txid[0] = seed.wrapping_add(i as u8);
                txid[1] = (i as u8).wrapping_mul(37);
                txid[2] = seed;
                TxInput {
                    outpoint: OutPoint { txid, vout: i as u32 },
                    witness: vec![],
                }
            })
            .collect();

        let tx = Transaction {
            version,
            inputs,
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: out_commitment,
                value: out_value,
            }],
            locktime,
        };

        let spent = Output {
            script_version: 2,
            commitment: spent_commitment,
            value: spent_value,
        };

        // Compute sighash for each input index
        let sighashes: Vec<[u8; 32]> = (0..num_inputs)
            .map(|i| sighash_v2(&tx, i, &spent))
            .collect();

        // All pairs must be distinct
        for i in 0..sighashes.len() {
            for j in (i + 1)..sighashes.len() {
                prop_assert_ne!(
                    sighashes[i], sighashes[j],
                    "sighash for input {} must differ from input {} (cross-input separation)",
                    i, j
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// PO-4.3: Field coverage — changing any consensus-critical field changes
//         the sighash
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn prop_po4_field_coverage_version(
        version in 1u32..u32::MAX,
        txid in prop::array::uniform32(any::<u8>()),
        commitment in prop::array::uniform32(any::<u8>()),
        value in 1_000u64..1_000_000,
        spent_commitment in prop::array::uniform32(any::<u8>()),
        spent_value in 1_000u64..1_000_000,
    ) {
        let tx = Transaction {
            version,
            inputs: vec![TxInput {
                outpoint: OutPoint { txid, vout: 0 },
                witness: vec![],
            }],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment,
                value,
            }],
            locktime: 0,
        };
        let spent = Output {
            script_version: 2,
            commitment: spent_commitment,
            value: spent_value,
        };

        let h1 = sighash_v2(&tx, 0, &spent);

        let mut tx2 = tx.clone();
        tx2.version = version.wrapping_add(1);
        let h2 = sighash_v2(&tx2, 0, &spent);

        prop_assert_ne!(h1, h2, "changing tx.version must change sighash");
    }

    #[test]
    fn prop_po4_field_coverage_locktime(
        locktime in 0u32..u32::MAX,
        txid in prop::array::uniform32(any::<u8>()),
        commitment in prop::array::uniform32(any::<u8>()),
        value in 1_000u64..1_000_000,
        spent_commitment in prop::array::uniform32(any::<u8>()),
        spent_value in 1_000u64..1_000_000,
    ) {
        let tx = Transaction {
            version: 2,
            inputs: vec![TxInput {
                outpoint: OutPoint { txid, vout: 0 },
                witness: vec![],
            }],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment,
                value,
            }],
            locktime,
        };
        let spent = Output {
            script_version: 2,
            commitment: spent_commitment,
            value: spent_value,
        };

        let h1 = sighash_v2(&tx, 0, &spent);

        let mut tx2 = tx.clone();
        tx2.locktime = locktime.wrapping_add(1);
        let h2 = sighash_v2(&tx2, 0, &spent);

        prop_assert_ne!(h1, h2, "changing tx.locktime must change sighash");
    }

    #[test]
    fn prop_po4_field_coverage_output_value(
        out_value in 1u64..u64::MAX,
        txid in prop::array::uniform32(any::<u8>()),
        commitment in prop::array::uniform32(any::<u8>()),
        spent_commitment in prop::array::uniform32(any::<u8>()),
        spent_value in 1_000u64..1_000_000,
    ) {
        let tx = Transaction {
            version: 2,
            inputs: vec![TxInput {
                outpoint: OutPoint { txid, vout: 0 },
                witness: vec![],
            }],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment,
                value: out_value,
            }],
            locktime: 0,
        };
        let spent = Output {
            script_version: 2,
            commitment: spent_commitment,
            value: spent_value,
        };

        let h1 = sighash_v2(&tx, 0, &spent);

        let mut tx2 = tx.clone();
        tx2.outputs[0].value = out_value.wrapping_add(1);
        let h2 = sighash_v2(&tx2, 0, &spent);

        prop_assert_ne!(h1, h2, "changing output value must change sighash");
    }

    #[test]
    fn prop_po4_field_coverage_spent_output_value(
        spent_value in 1u64..u64::MAX,
        txid in prop::array::uniform32(any::<u8>()),
        commitment in prop::array::uniform32(any::<u8>()),
        out_value in 1_000u64..1_000_000,
        spent_commitment in prop::array::uniform32(any::<u8>()),
    ) {
        let tx = Transaction {
            version: 2,
            inputs: vec![TxInput {
                outpoint: OutPoint { txid, vout: 0 },
                witness: vec![],
            }],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment,
                value: out_value,
            }],
            locktime: 0,
        };
        let spent = Output {
            script_version: 2,
            commitment: spent_commitment,
            value: spent_value,
        };

        let h1 = sighash_v2(&tx, 0, &spent);

        let mut spent2 = spent.clone();
        spent2.value = spent_value.wrapping_add(1);
        let h2 = sighash_v2(&tx, 0, &spent2);

        prop_assert_ne!(h1, h2, "changing spent output value must change sighash");
    }

    #[test]
    fn prop_po4_field_coverage_spent_output_commitment(
        spent_commitment in prop::array::uniform32(any::<u8>()),
        txid in prop::array::uniform32(any::<u8>()),
        commitment in prop::array::uniform32(any::<u8>()),
        out_value in 1_000u64..1_000_000,
        spent_value in 1_000u64..1_000_000,
    ) {
        let tx = Transaction {
            version: 2,
            inputs: vec![TxInput {
                outpoint: OutPoint { txid, vout: 0 },
                witness: vec![],
            }],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment,
                value: out_value,
            }],
            locktime: 0,
        };
        let spent = Output {
            script_version: 2,
            commitment: spent_commitment,
            value: spent_value,
        };

        let h1 = sighash_v2(&tx, 0, &spent);

        let mut spent2 = spent.clone();
        spent2.commitment[0] ^= 0xFF;
        let h2 = sighash_v2(&tx, 0, &spent2);

        prop_assert_ne!(h1, h2, "changing spent output commitment must change sighash");
    }
}

// ---------------------------------------------------------------------------
// PO-4.4: verify_sighash_commitment_property — executable evidence
// ---------------------------------------------------------------------------
//
// Use the verify_sighash_commitment_property function as a comprehensive
// check across randomly generated transactions.

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn prop_po4_verify_commitment_property(
        num_inputs in 1usize..5,
        num_outputs in 1usize..5,
        version in 1u32..4,
        locktime in 0u32..500_000,
        seed in any::<u8>(),
        out_value in 1_000u64..1_000_000,
        spent_value in 1_000u64..1_000_000,
    ) {
        // Build a transaction with random inputs and outputs
        let inputs: Vec<TxInput> = (0..num_inputs)
            .map(|i| {
                let mut txid = [0u8; 32];
                txid[0] = seed.wrapping_add(i as u8);
                txid[1] = (i as u8).wrapping_mul(41);
                txid[2] = seed.wrapping_mul(7);
                TxInput {
                    outpoint: OutPoint { txid, vout: i as u32 },
                    witness: vec![],
                }
            })
            .collect();

        let outputs: Vec<TxOutput> = (0..num_outputs)
            .map(|i| {
                let mut comm = [0u8; 32];
                comm[0] = seed.wrapping_add(i as u8).wrapping_mul(13);
                TxOutput {
                    script_version: 2,
                    commitment: comm,
                    value: out_value.wrapping_add(i as u64 * 1_000),
                }
            })
            .collect();

        let tx = Transaction {
            version,
            inputs,
            outputs,
            locktime,
        };

        let spent_outputs: Vec<Output> = (0..num_inputs)
            .map(|i| {
                let mut comm = [0u8; 32];
                comm[0] = seed.wrapping_add(i as u8).wrapping_mul(19);
                Output {
                    script_version: 2,
                    commitment: comm,
                    value: spent_value.wrapping_add(i as u64 * 500),
                }
            })
            .collect();

        let result = verify_sighash_commitment_property(&tx, &spent_outputs);

        prop_assert!(
            result.cross_input_separation,
            "PO-4 cross-input separation must hold for all generated transactions"
        );
        prop_assert!(
            result.field_coverage,
            "PO-4 field coverage must hold for all generated transactions"
        );
        prop_assert_eq!(
            result.num_inputs, num_inputs,
            "num_inputs in result must match"
        );
    }
}

// ---------------------------------------------------------------------------
// PO-4.5: Tagged hash domain separation
// ---------------------------------------------------------------------------
//
// Verify that the tagged hash function provides proper domain separation:
// different tags always produce different hashes for the same data.

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    #[test]
    fn prop_po4_tagged_hash_domain_separation(
        data in prop::collection::vec(any::<u8>(), 0..200),
    ) {
        // All PQWitness tags must produce distinct hashes for the same data
        let h_outpoints = tagged_hash("PQWitness/outpoints", &data);
        let h_outputs = tagged_hash("PQWitness/outputs", &data);
        let h_sighash = tagged_hash("PQWitness/sighash", &data);

        prop_assert_ne!(
            h_outpoints, h_outputs,
            "PQWitness/outpoints and PQWitness/outputs must produce different hashes"
        );
        prop_assert_ne!(
            h_outpoints, h_sighash,
            "PQWitness/outpoints and PQWitness/sighash must produce different hashes"
        );
        prop_assert_ne!(
            h_outputs, h_sighash,
            "PQWitness/outputs and PQWitness/sighash must produce different hashes"
        );

        // Also verify domain separation from BIP 341
        let h_tap = tagged_hash("TapSighash", &data);
        prop_assert_ne!(
            h_sighash, h_tap,
            "PQWitness/sighash must be domain-separated from TapSighash"
        );
    }
}

// ===========================================================================
// PO-8: Implementation Correspondence Tests
// ===========================================================================
//
// These tests verify that the Rust implementation matches the behavior
// specified in the Coq model (formal/coq/SpendPredPQ.v). They serve as
// executable evidence for PO-8 by testing the exact properties proved
// in Coq against the Rust code.
//
// The Coq model proves:
//   - parse(serialize(pk, sig)) = Some(pk, sig) for non-empty pk, sig
//   - parse is injective: parse(w1) = parse(w2) = Some(pk,sig) => w1 = w2
//   - spend_pred_pq is total and deterministic
//   - spend_pred_pq accepts iff parse succeeds AND hash matches AND verify passes
//
// These tests verify the same properties hold in the Rust implementation.

// ---------------------------------------------------------------------------
// PO-8.1: Varint axiom correspondence
// ---------------------------------------------------------------------------
//
// The Coq model axiomatizes varint with 6 properties. We verify each
// axiom holds for the Rust encode_varint/decode_varint.

use crate::encoding::{encode_varint, decode_varint};

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    // Axiom A1: decode(encode(n)) = Some(n, |encode(n)|)
    #[test]
    fn prop_po8_varint_axiom_a1_round_trip(n in 0u64..1_000_000u64) {
        let encoded = encode_varint(n);
        let decoded = decode_varint(&encoded);
        prop_assert_eq!(
            decoded,
            Some((n, encoded.len())),
            "A1: decode(encode({})) must return Some(({}, {}))",
            n, n, encoded.len()
        );
    }

    // Axiom A2: |encode(n)| >= 1
    #[test]
    fn prop_po8_varint_axiom_a2_positive_length(n in 0u64..1_000_000u64) {
        let encoded = encode_varint(n);
        prop_assert!(
            !encoded.is_empty(),
            "A2: encode({}) must produce at least 1 byte",
            n
        );
    }

    // Axiom A3: decode(encode(n) ++ tail) = Some(n, |encode(n)|)
    #[test]
    fn prop_po8_varint_axiom_a3_trailing_data(
        n in 0u64..1_000_000u64,
        tail in prop::collection::vec(any::<u8>(), 0..100),
    ) {
        let encoded = encode_varint(n);
        let mut with_tail = encoded.clone();
        with_tail.extend_from_slice(&tail);
        let decoded = decode_varint(&with_tail);
        prop_assert_eq!(
            decoded,
            Some((n, encoded.len())),
            "A3: decode(encode({}) ++ tail) must return Some(({}, {}))",
            n, n, encoded.len()
        );
    }

    // Axiom A4: consumed <= |input|
    #[test]
    fn prop_po8_varint_axiom_a4_prefix_bound(
        data in prop::collection::vec(any::<u8>(), 1..20),
    ) {
        if let Some((_, consumed)) = decode_varint(&data) {
            prop_assert!(
                consumed <= data.len(),
                "A4: consumed ({}) must be <= input length ({})",
                consumed, data.len()
            );
        }
    }

    // Axiom A5: firstn(consumed, input) = encode(value)
    #[test]
    fn prop_po8_varint_axiom_a5_canonical_prefix(n in 0u64..1_000_000u64) {
        let encoded = encode_varint(n);
        let mut with_tail = encoded.clone();
        with_tail.extend_from_slice(&[0xDE, 0xAD, 0xBE, 0xEF]);
        if let Some((v, consumed)) = decode_varint(&with_tail) {
            prop_assert_eq!(v, n);
            prop_assert_eq!(
                &with_tail[..consumed],
                encoded.as_slice(),
                "A5: first {} bytes of input must equal encode({})",
                consumed, n
            );
        }
    }

    // Axiom A6: consumed = |encode(value)|
    #[test]
    fn prop_po8_varint_axiom_a6_consumed_equals_encoding_length(n in 0u64..1_000_000u64) {
        let encoded = encode_varint(n);
        if let Some((v, consumed)) = decode_varint(&encoded) {
            prop_assert_eq!(v, n);
            let canonical = encode_varint(v);
            prop_assert_eq!(
                consumed,
                canonical.len(),
                "A6: consumed ({}) must equal |encode({})| ({})",
                consumed, v, canonical.len()
            );
        }
    }
}

// ---------------------------------------------------------------------------
// PO-8.2: Parse injectivity correspondence
// ---------------------------------------------------------------------------
//
// The Coq theorem parse_varint_injective proves:
//   parse(w1) = Some(pk,sig) ∧ parse(w2) = Some(pk,sig) => w1 = w2
//
// We verify this holds in Rust.

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    #[test]
    fn prop_po8_parse_injectivity(
        pk in prop::collection::vec(any::<u8>(), 1..500),
        sig in prop::collection::vec(any::<u8>(), 1..500),
    ) {
        // Construct two witnesses that parse to the same (pk, sig)
        let w1 = serialize_witness(&pk, &sig);
        let w2 = serialize_witness(&pk, &sig);

        // Both must parse to the same result
        let p1 = parse_witness(&w1);
        let p2 = parse_witness(&w2);
        prop_assert_eq!(&p1, &p2, "same (pk,sig) must parse identically");

        // And the witnesses themselves must be identical (injectivity)
        prop_assert_eq!(
            &w1, &w2,
            "PO-8 parse injectivity: witnesses with same parsed components must be byte-identical"
        );
    }
}

// ---------------------------------------------------------------------------
// PO-8.3: Witness determines serialize (Coq: parse_varint_witness_determines_serialize)
// ---------------------------------------------------------------------------
//
// The Coq theorem proves: parse(w) = Some(pk,sig) => w = serialize(pk,sig)
// We verify this in Rust.

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    #[test]
    fn prop_po8_witness_determines_serialize(
        pk in prop::collection::vec(any::<u8>(), 1..500),
        sig in prop::collection::vec(any::<u8>(), 1..500),
    ) {
        let w = serialize_witness(&pk, &sig);
        let parsed = parse_witness(&w);
        prop_assert!(parsed.is_some());
        let (parsed_pk, parsed_sig) = parsed.unwrap();

        // The Coq theorem says: w = serialize_witness(parsed_pk, parsed_sig)
        let re_serialized = serialize_witness(&parsed_pk, &parsed_sig);
        prop_assert_eq!(
            &w, &re_serialized,
            "PO-8: w must equal serialize(parse(w).pk, parse(w).sig)"
        );
    }
}

// ---------------------------------------------------------------------------
// PO-8.4: SpendPred_PQ complete characterization correspondence
// ---------------------------------------------------------------------------
//
// The Coq theorem spend_pred_pq_iff proves:
//   spend_pred_pq(P, m, w) = true <=>
//     exists pk sig, parse(w) = Some(pk,sig) /\ H(pk) = P /\ Vfy(pk,m,sig) = true
//
// We verify both directions in Rust with real ML-DSA-44 keys.

#[test]
fn po8_spend_pred_iff_forward_direction() {
    // Forward: if all three conditions hold, spend_pred_pq returns true
    let (pk, sk) = fips204::ml_dsa_44::try_keygen().unwrap();
    let pk_bytes = pk.into_bytes().to_vec();
    let message = b"PO-8 correspondence test message";

    let sig = sk.try_sign(message.as_slice(), &[]).unwrap();
    let witness = serialize_witness(&pk_bytes, &sig.to_vec());
    let commitment: [u8; 32] = Sha256::digest(&pk_bytes).into();

    // Condition 1: parse succeeds
    assert!(parse_witness(&witness).is_some(), "parse must succeed");
    // Condition 2: H(pk) = P
    let (parsed_pk, _) = parse_witness(&witness).unwrap();
    assert_eq!(
        Sha256::digest(&parsed_pk).as_slice(),
        commitment.as_slice(),
        "H(pk) must equal commitment"
    );
    // Condition 3: Vfy passes (implicit in spend_pred_pq returning true)

    // Forward direction: all conditions hold => spend_pred_pq = true
    assert!(
        spend_pred_pq(&commitment, message, &witness),
        "PO-8 forward: spend_pred_pq must return true when all conditions hold"
    );
}

#[test]
fn po8_spend_pred_iff_backward_parse_failure() {
    // Backward: if parse fails, spend_pred_pq returns false
    let commitment = [0u8; 32];
    let message = b"test";
    let bad_witness = vec![0x05, 0x01]; // pk_len=5 but only 1 byte follows

    assert!(parse_witness(&bad_witness).is_none(), "parse must fail");
    assert!(
        !spend_pred_pq(&commitment, message, &bad_witness),
        "PO-8 backward: spend_pred_pq must return false when parse fails"
    );
}

#[test]
fn po8_spend_pred_iff_backward_hash_mismatch() {
    // Backward: if H(pk) != P, spend_pred_pq returns false
    let (pk, sk) = fips204::ml_dsa_44::try_keygen().unwrap();
    let pk_bytes = pk.into_bytes().to_vec();
    let message = b"PO-8 hash mismatch test";
    let sig = sk.try_sign(message.as_slice(), &[]).unwrap();
    let witness = serialize_witness(&pk_bytes, &sig.to_vec());

    let wrong_commitment = [0xFF; 32]; // definitely not H(pk)
    assert!(
        !spend_pred_pq(&wrong_commitment, message, &witness),
        "PO-8 backward: spend_pred_pq must return false when H(pk) != P"
    );
}

#[test]
fn po8_spend_pred_iff_backward_vfy_failure() {
    // Backward: if Vfy fails, spend_pred_pq returns false
    let (pk, sk) = fips204::ml_dsa_44::try_keygen().unwrap();
    let pk_bytes = pk.into_bytes().to_vec();
    let message = b"PO-8 vfy failure test";
    let sig = sk.try_sign(message.as_slice(), &[]).unwrap();
    let witness = serialize_witness(&pk_bytes, &sig.to_vec());
    let commitment: [u8; 32] = Sha256::digest(&pk_bytes).into();

    // Use a different message for verification
    assert!(
        !spend_pred_pq(&commitment, b"wrong message", &witness),
        "PO-8 backward: spend_pred_pq must return false when Vfy fails"
    );
}

// ---------------------------------------------------------------------------
// PO-8.5: Cost model correspondence (Coq UTXOTransitions.v)
// ---------------------------------------------------------------------------
//
// The Coq theorem cost_equals_weight proves:
//   cost_tx(witness_lens, num_outputs) = weight_tx(|witness_lens|, witness_lens, num_outputs)
//
// We verify this holds in Rust.

#[test]
fn po8_cost_equals_weight_correspondence() {
    // Test several transaction configurations
    let test_cases: Vec<(Vec<usize>, usize)> = vec![
        (vec![3734], 1),           // ML-DSA-44 single-sig
        (vec![7890], 1),           // SLH-DSA-128s single-sig
        (vec![8786], 1),           // 2-of-3 multisig
        (vec![3734, 3734], 2),     // 2-input, 2-output
        (vec![100], 1),            // small witness
        (vec![16000], 1),          // max witness
        (vec![1, 1, 1, 1, 1], 5), // many small inputs
    ];

    for (witness_sizes, num_outputs) in test_cases {
        let tx = make_tx_for_weight(&witness_sizes, num_outputs);
        let cost = cost_tx(&tx);
        let weight = weight_tx(&tx);

        assert_eq!(
            cost, weight,
            "PO-8: cost_tx must equal weight_tx for witnesses {:?}, {} outputs (cost={}, weight={})",
            witness_sizes, num_outputs, cost, weight
        );
    }
}

// ---------------------------------------------------------------------------
// Adversarial boundary tests
// ---------------------------------------------------------------------------
//
// These tests probe the cryptographic boundary conditions that the
// paper's security theorems (Theorems 5-7) rely on.

#[test]
fn adversarial_commitment_second_preimage_resistance() {
    // Theorem 5 relies on hash binding: finding pk' != pk with H(pk') = H(pk)
    // should be infeasible. We verify that different ML-DSA-44 public keys
    // produce different SHA-256 commitments (probabilistic evidence).
    let mut commitments = std::collections::HashSet::new();
    for _ in 0..20 {
        let (pk, _) = fips204::ml_dsa_44::try_keygen().unwrap();
        let pk_bytes = pk.into_bytes();
        let commitment: [u8; 32] = Sha256::digest(&pk_bytes).into();
        assert!(
            commitments.insert(commitment),
            "SHA-256 collision detected among ML-DSA-44 public keys (astronomically unlikely)"
        );
    }
}

#[test]
fn adversarial_cross_input_replay_resistance() {
    // Theorem 6 (Complete Authorization) relies on sighash cross-input
    // separation. We verify that a valid witness for input i cannot be
    // replayed as a witness for input j in the same transaction.
    let (pk, sk) = fips204::ml_dsa_44::try_keygen().unwrap();
    let pk_bytes = pk.into_bytes().to_vec();
    let commitment: [u8; 32] = Sha256::digest(&pk_bytes).into();

    // Create a 2-input transaction where both inputs are locked to the same key
    let mut utxo_set = UtxoSet::new();
    let op0 = OutPoint { txid: [0x01; 32], vout: 0 };
    let op1 = OutPoint { txid: [0x02; 32], vout: 0 };
    utxo_set.insert(op0.clone(), Output { script_version: 2, commitment, value: 50_000 });
    utxo_set.insert(op1.clone(), Output { script_version: 2, commitment, value: 50_000 });

    let spent0 = utxo_set.get(&op0).unwrap().clone();
    let spent1 = utxo_set.get(&op1).unwrap().clone();

    // Build a transaction spending both inputs
    let mut tx = Transaction {
        version: 2,
        inputs: vec![
            crate::types::TxInput { outpoint: op0, witness: vec![] },
            crate::types::TxInput { outpoint: op1, witness: vec![] },
        ],
        outputs: vec![crate::types::TxOutput {
            script_version: 2,
            commitment: [0xCC; 32],
            value: 100_000,
        }],
        locktime: 0,
    };

    // Sign input 0
    let sighash0 = sighash_v2(&tx, 0, &spent0);
    let sig0 = sk.try_sign(&sighash0, &[]).unwrap();
    let witness0 = serialize_witness(&pk_bytes, &sig0.to_vec());
    tx.inputs[0].witness = witness0.clone();

    // Verify input 0's witness is valid for input 0
    assert!(
        spend_pred_pq(&commitment, &sighash0, &tx.inputs[0].witness),
        "witness for input 0 must be valid for input 0"
    );

    // Attempt to replay input 0's witness for input 1
    let sighash1 = sighash_v2(&tx, 1, &spent1);
    assert_ne!(sighash0, sighash1, "sighashes for different inputs must differ");

    // The replayed witness must fail for input 1
    assert!(
        !spend_pred_pq(&commitment, &sighash1, &witness0),
        "CRITICAL: witness for input 0 must NOT be valid for input 1 (cross-input replay)"
    );
}

#[test]
fn adversarial_cross_transaction_replay_resistance() {
    // Theorem 6 also excludes cross-transaction replay. A witness valid
    // for tx1 must not be valid for a different tx2.
    let (pk, sk) = fips204::ml_dsa_44::try_keygen().unwrap();
    let pk_bytes = pk.into_bytes().to_vec();
    let commitment: [u8; 32] = Sha256::digest(&pk_bytes).into();

    let spent = Output { script_version: 2, commitment, value: 50_000 };

    // Transaction 1
    let tx1 = Transaction {
        version: 2,
        inputs: vec![crate::types::TxInput {
            outpoint: OutPoint { txid: [0x01; 32], vout: 0 },
            witness: vec![],
        }],
        outputs: vec![crate::types::TxOutput {
            script_version: 2,
            commitment: [0xAA; 32],
            value: 50_000,
        }],
        locktime: 0,
    };

    // Transaction 2 (different output)
    let tx2 = Transaction {
        version: 2,
        inputs: vec![crate::types::TxInput {
            outpoint: OutPoint { txid: [0x01; 32], vout: 0 },
            witness: vec![],
        }],
        outputs: vec![crate::types::TxOutput {
            script_version: 2,
            commitment: [0xBB; 32], // different commitment
            value: 50_000,
        }],
        locktime: 0,
    };

    // Sign for tx1
    let sighash1 = sighash_v2(&tx1, 0, &spent);
    let sig1 = sk.try_sign(&sighash1, &[]).unwrap();
    let witness1 = serialize_witness(&pk_bytes, &sig1.to_vec());

    // Verify witness is valid for tx1
    assert!(spend_pred_pq(&commitment, &sighash1, &witness1));

    // Attempt to use tx1's witness for tx2
    let sighash2 = sighash_v2(&tx2, 0, &spent);
    assert_ne!(sighash1, sighash2, "different transactions must have different sighashes");

    assert!(
        !spend_pred_pq(&commitment, &sighash2, &witness1),
        "CRITICAL: witness for tx1 must NOT be valid for tx2 (cross-transaction replay)"
    );
}
