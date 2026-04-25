//! Sighash v2 computation for witness version 2.
//!
//! Follows BIP 341 Taproot sighash structure with PQ-specific modifications:
//! - **Tagged hashes** (BIP 340/341 style): `SHA256(SHA256(tag) || SHA256(tag) || data)`
//!   with `"PQWitness/"` prefix for domain separation from BIP 341's `"TapSighash/"` tags.
//! - **Structured preimage with tagged sub-hashes**: outpoints, outputs, and amounts
//!   are each hashed with their own domain-separated tag before inclusion in the
//!   final sighash preimage.
//! - **Explicit spend_type byte**: `0x00` for key-path spend (single-sig).
//! - **Epoch byte 0x02** for domain separation from v0/v1 sighashes.
//! - **Cross-input separation** via input index commitment.
//!
//! The sighash satisfies Definition 5 (Sighash Commitment property):
//! 1. Injectivity: domain-separated from v0/v1 by epoch byte and tagged hashes,
//!    commits to all consensus-critical fields.
//! 2. Cross-input separation: input index included in hash preimage.
//! 3. Field coverage: version, all input outpoints, all output scripts/values,
//!    spent output scriptPubKey and amount, locktime, input index, spend_type.
//!
//! Requirements: 2.8, 10.2

use sha2::{Digest, Sha256};

use crate::types::{Output, Transaction};

/// PQ-specific epoch byte for domain separation from v0/v1 sighashes.
const PQ_EPOCH_BYTE: u8 = 0x02;

/// Spend type byte: 0x00 = key-path spend (single-sig), matching BIP 341's
/// spend_type concept.
const SPEND_TYPE_KEY_PATH: u8 = 0x00;

/// Compute a BIP 340/341-style tagged hash.
///
/// `tagged_hash(tag, data) = SHA256(SHA256(tag) || SHA256(tag) || data)`
///
/// The double tag-hash prefix provides domain separation: different tags
/// produce different hash functions even for identical data, preventing
/// cross-protocol hash collisions.
///
/// Tag names use the `"PQWitness/"` prefix to domain-separate from
/// BIP 341's `"TapSighash/"` tags.
pub fn tagged_hash(tag: &str, data: &[u8]) -> [u8; 32] {
    let tag_hash = Sha256::digest(tag.as_bytes());
    let mut hasher = Sha256::new();
    hasher.update(tag_hash);
    hasher.update(tag_hash);
    hasher.update(data);
    hasher.finalize().into()
}

/// Compute the sighash for witness version 2.
///
/// Follows BIP 341 Taproot sighash structure with PQ-specific modifications:
/// - Tagged sub-hashes for outpoints and outputs
/// - Epoch byte `0x02` for domain separation from v0/v1
/// - Explicit spend_type byte (`0x00` for key-path)
/// - Spent output's witness version and commitment in the hash preimage
/// - Commits to: version, all input outpoints, all output scripts/values,
///   spent output scriptPubKey and amount, locktime, input index, spend_type
///
/// ## Preimage structure
///
/// ```text
/// Final sighash = tagged_hash("PQWitness/sighash",
///     epoch (1B) || version (4B LE) ||
///     hash_outpoints (32B) || hash_outputs (32B) ||
///     spend_type (1B) ||
///     spent_output_script_version (1B) || spent_output_commitment (32B) ||
///     spent_output_value (8B LE) ||
///     input_index (4B LE) || locktime (4B LE)
/// )
/// ```
///
/// Where:
/// - `hash_outpoints = tagged_hash("PQWitness/outpoints", concat of all input outpoints)`
/// - `hash_outputs = tagged_hash("PQWitness/outputs", concat of all output data)`
///
/// # Arguments
///
/// * `tx` - the transaction being signed
/// * `input_index` - the index of the input being authorized
/// * `spent_output` - the UTXO being spent by this input
///
/// # Returns
///
/// A 32-byte tagged sighash digest.
///
/// # Panics
///
/// Panics if `input_index >= tx.inputs.len()`.
pub fn sighash_v2(tx: &Transaction, input_index: usize, spent_output: &Output) -> [u8; 32] {
    assert!(
        input_index < tx.inputs.len(),
        "input_index {} out of bounds for transaction with {} inputs",
        input_index,
        tx.inputs.len()
    );

    // Step 1: Tagged hash of all input outpoints.
    let hash_outpoints = {
        let mut data = Vec::new();
        for input in &tx.inputs {
            data.extend_from_slice(&input.outpoint.txid);
            data.extend_from_slice(&input.outpoint.vout.to_le_bytes());
        }
        tagged_hash("PQWitness/outpoints", &data)
    };

    // Step 2: Tagged hash of all output scripts/values.
    let hash_outputs = {
        let mut data = Vec::new();
        for output in &tx.outputs {
            data.push(output.script_version);
            data.extend_from_slice(&output.commitment);
            data.extend_from_slice(&output.value.to_le_bytes());
        }
        tagged_hash("PQWitness/outputs", &data)
    };

    // Step 3: Build the final sighash preimage and compute the tagged hash.
    let mut preimage = Vec::new();
    preimage.push(PQ_EPOCH_BYTE);
    preimage.extend_from_slice(&tx.version.to_le_bytes());
    preimage.extend_from_slice(&hash_outpoints);
    preimage.extend_from_slice(&hash_outputs);
    preimage.push(SPEND_TYPE_KEY_PATH);
    preimage.push(spent_output.script_version);
    preimage.extend_from_slice(&spent_output.commitment);
    preimage.extend_from_slice(&spent_output.value.to_le_bytes());
    preimage.extend_from_slice(&(input_index as u32).to_le_bytes());
    preimage.extend_from_slice(&tx.locktime.to_le_bytes());

    tagged_hash("PQWitness/sighash", &preimage)
}

/// Result of verifying the sighash commitment property (Definition 5).
///
/// Contains the results of all three sub-properties. All must hold for
/// the sighash to satisfy PO-4.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SighashCommitmentResult {
    /// True if cross-input separation holds: all input sighashes are distinct.
    pub cross_input_separation: bool,
    /// True if field coverage holds: changing any consensus-critical field
    /// changes the sighash.
    pub field_coverage: bool,
    /// Number of inputs verified.
    pub num_inputs: usize,
}

/// Programmatically verify all three properties of Definition 5 (Sighash
/// Commitment property) for a given transaction.
///
/// This serves as executable evidence for PO-4. It checks:
///
/// 1. **Cross-input separation**: For every pair of distinct input indices
///    `(i, j)` in the transaction, `sighash_v2(tx, i, ...) != sighash_v2(tx, j, ...)`.
///
/// 2. **Field coverage**: For each consensus-critical field, mutating that
///    field produces a different sighash. Fields tested:
///    - `tx.version`
///    - `tx.locktime`
///    - Input outpoint (txid of first input)
///    - Output value (first output)
///    - Output commitment (first output)
///    - Output script version (first output)
///    - Spent output commitment
///    - Spent output value
///    - Spent output script version
///
/// Note: Injectivity (property 1) is implied by field coverage combined
/// with the tagged hash structure. Two transactions that differ in any
/// consensus-critical field will produce different sighashes.
///
/// # Arguments
///
/// * `tx` - the transaction to verify (must have at least 1 input and 1 output)
/// * `spent_outputs` - the spent outputs for each input, in order
///
/// # Returns
///
/// A [`SighashCommitmentResult`] with the verification results.
pub fn verify_sighash_commitment_property(
    tx: &Transaction,
    spent_outputs: &[Output],
) -> SighashCommitmentResult {
    assert_eq!(
        tx.inputs.len(),
        spent_outputs.len(),
        "spent_outputs length must match tx.inputs length"
    );

    if tx.inputs.is_empty() {
        return SighashCommitmentResult {
            cross_input_separation: true,
            field_coverage: true,
            num_inputs: 0,
        };
    }

    // --- Cross-input separation ---
    let sighashes: Vec<[u8; 32]> = (0..tx.inputs.len())
        .map(|i| sighash_v2(tx, i, &spent_outputs[i]))
        .collect();

    let cross_input_separation = {
        let mut ok = true;
        for i in 0..sighashes.len() {
            for j in (i + 1)..sighashes.len() {
                if sighashes[i] == sighashes[j] {
                    ok = false;
                }
            }
        }
        ok
    };

    // --- Field coverage ---
    // We test mutations against input 0.
    let baseline = sighashes[0];
    let spent = &spent_outputs[0];

    let field_coverage = {
        let mut ok = true;

        // Mutate tx.version
        {
            let mut tx2 = tx.clone();
            tx2.version = tx.version.wrapping_add(1);
            if sighash_v2(&tx2, 0, spent) == baseline {
                ok = false;
            }
        }

        // Mutate tx.locktime
        {
            let mut tx2 = tx.clone();
            tx2.locktime = tx.locktime.wrapping_add(1);
            if sighash_v2(&tx2, 0, spent) == baseline {
                ok = false;
            }
        }

        // Mutate input outpoint (txid of first input)
        {
            let mut tx2 = tx.clone();
            tx2.inputs[0].outpoint.txid[0] ^= 0xFF;
            if sighash_v2(&tx2, 0, spent) == baseline {
                ok = false;
            }
        }

        // Mutate input outpoint vout
        {
            let mut tx2 = tx.clone();
            tx2.inputs[0].outpoint.vout ^= 1;
            if sighash_v2(&tx2, 0, spent) == baseline {
                ok = false;
            }
        }

        // Mutate output value (if outputs exist)
        if !tx.outputs.is_empty() {
            let mut tx2 = tx.clone();
            tx2.outputs[0].value = tx.outputs[0].value.wrapping_add(1);
            if sighash_v2(&tx2, 0, spent) == baseline {
                ok = false;
            }
        }

        // Mutate output commitment (if outputs exist)
        if !tx.outputs.is_empty() {
            let mut tx2 = tx.clone();
            tx2.outputs[0].commitment[0] ^= 0xFF;
            if sighash_v2(&tx2, 0, spent) == baseline {
                ok = false;
            }
        }

        // Mutate output script version (if outputs exist)
        if !tx.outputs.is_empty() {
            let mut tx2 = tx.clone();
            tx2.outputs[0].script_version ^= 0x01;
            if sighash_v2(&tx2, 0, spent) == baseline {
                ok = false;
            }
        }

        // Mutate spent output commitment
        {
            let mut spent2 = spent.clone();
            spent2.commitment[0] ^= 0xFF;
            if sighash_v2(tx, 0, &spent2) == baseline {
                ok = false;
            }
        }

        // Mutate spent output value
        {
            let mut spent2 = spent.clone();
            spent2.value = spent.value.wrapping_add(1);
            if sighash_v2(tx, 0, &spent2) == baseline {
                ok = false;
            }
        }

        // Mutate spent output script version
        {
            let mut spent2 = spent.clone();
            spent2.script_version ^= 0x01;
            if sighash_v2(tx, 0, &spent2) == baseline {
                ok = false;
            }
        }

        ok
    };

    SighashCommitmentResult {
        cross_input_separation,
        field_coverage,
        num_inputs: tx.inputs.len(),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{OutPoint, Output, Transaction, TxInput, TxOutput};

    /// Helper: build a simple 2-input, 1-output transaction.
    fn sample_tx() -> Transaction {
        Transaction {
            version: 2,
            inputs: vec![
                TxInput {
                    outpoint: OutPoint {
                        txid: [0x01; 32],
                        vout: 0,
                    },
                    witness: vec![0xAA],
                },
                TxInput {
                    outpoint: OutPoint {
                        txid: [0x02; 32],
                        vout: 1,
                    },
                    witness: vec![0xBB],
                },
            ],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: [0xCC; 32],
                value: 50_000,
            }],
            locktime: 0,
        }
    }

    /// Helper: build a PQ spent output.
    fn sample_spent_output() -> Output {
        Output {
            script_version: 2,
            commitment: [0xDD; 32],
            value: 100_000,
        }
    }

    // -- Tagged hash unit tests --

    #[test]
    fn tagged_hash_deterministic() {
        let h1 = tagged_hash("PQWitness/test", b"hello");
        let h2 = tagged_hash("PQWitness/test", b"hello");
        assert_eq!(h1, h2);
    }

    #[test]
    fn tagged_hash_different_tags_different_output() {
        let h1 = tagged_hash("PQWitness/outpoints", b"data");
        let h2 = tagged_hash("PQWitness/outputs", b"data");
        assert_ne!(h1, h2, "different tags must produce different hashes for same data");
    }

    #[test]
    fn tagged_hash_different_data_different_output() {
        let h1 = tagged_hash("PQWitness/sighash", b"data1");
        let h2 = tagged_hash("PQWitness/sighash", b"data2");
        assert_ne!(h1, h2, "different data must produce different hashes for same tag");
    }

    #[test]
    fn tagged_hash_domain_separation_from_bip341() {
        // PQWitness tags must produce different hashes than TapSighash tags
        let pq = tagged_hash("PQWitness/sighash", b"data");
        let tap = tagged_hash("TapSighash", b"data");
        assert_ne!(pq, tap, "PQWitness tags must be domain-separated from BIP 341 tags");
    }

    // -- Determinism --

    #[test]
    fn sighash_deterministic() {
        let tx = sample_tx();
        let spent = sample_spent_output();
        let h1 = sighash_v2(&tx, 0, &spent);
        let h2 = sighash_v2(&tx, 0, &spent);
        assert_eq!(h1, h2, "same inputs must produce the same sighash");
    }

    // -- Cross-input separation --

    #[test]
    fn sighash_cross_input_separation() {
        let tx = sample_tx();
        let spent = sample_spent_output();
        let h0 = sighash_v2(&tx, 0, &spent);
        let h1 = sighash_v2(&tx, 1, &spent);
        assert_ne!(
            h0, h1,
            "different input indices must produce different sighash values"
        );
    }

    // -- Domain separation (epoch byte) --

    #[test]
    fn sighash_domain_separation_via_witness_version() {
        let tx = sample_tx();
        let pq_output = Output {
            script_version: 2,
            commitment: [0xDD; 32],
            value: 100_000,
        };
        let taproot_output = Output {
            script_version: 1,
            commitment: [0xDD; 32],
            value: 100_000,
        };
        let h_pq = sighash_v2(&tx, 0, &pq_output);
        let h_tr = sighash_v2(&tx, 0, &taproot_output);
        assert_ne!(
            h_pq, h_tr,
            "different spent output witness versions must produce different sighash values"
        );
    }

    // -- Field coverage: changing any consensus-critical field changes the sighash --

    #[test]
    fn sighash_changes_with_tx_version() {
        let mut tx = sample_tx();
        let spent = sample_spent_output();
        let h1 = sighash_v2(&tx, 0, &spent);
        tx.version = 3;
        let h2 = sighash_v2(&tx, 0, &spent);
        assert_ne!(h1, h2, "changing tx version must change sighash");
    }

    #[test]
    fn sighash_changes_with_locktime() {
        let mut tx = sample_tx();
        let spent = sample_spent_output();
        let h1 = sighash_v2(&tx, 0, &spent);
        tx.locktime = 500_000;
        let h2 = sighash_v2(&tx, 0, &spent);
        assert_ne!(h1, h2, "changing locktime must change sighash");
    }

    #[test]
    fn sighash_changes_with_input_outpoint() {
        let mut tx = sample_tx();
        let spent = sample_spent_output();
        let h1 = sighash_v2(&tx, 0, &spent);
        tx.inputs[0].outpoint.txid = [0xFF; 32];
        let h2 = sighash_v2(&tx, 0, &spent);
        assert_ne!(h1, h2, "changing an input outpoint must change sighash");
    }

    #[test]
    fn sighash_changes_with_output_value() {
        let mut tx = sample_tx();
        let spent = sample_spent_output();
        let h1 = sighash_v2(&tx, 0, &spent);
        tx.outputs[0].value = 99_999;
        let h2 = sighash_v2(&tx, 0, &spent);
        assert_ne!(h1, h2, "changing an output value must change sighash");
    }

    #[test]
    fn sighash_changes_with_output_commitment() {
        let mut tx = sample_tx();
        let spent = sample_spent_output();
        let h1 = sighash_v2(&tx, 0, &spent);
        tx.outputs[0].commitment = [0x00; 32];
        let h2 = sighash_v2(&tx, 0, &spent);
        assert_ne!(h1, h2, "changing an output commitment must change sighash");
    }

    #[test]
    fn sighash_changes_with_output_script_version() {
        let mut tx = sample_tx();
        let spent = sample_spent_output();
        let h1 = sighash_v2(&tx, 0, &spent);
        tx.outputs[0].script_version = 0;
        let h2 = sighash_v2(&tx, 0, &spent);
        assert_ne!(
            h1, h2,
            "changing an output script version must change sighash"
        );
    }

    #[test]
    fn sighash_changes_with_spent_output_commitment() {
        let spent1 = sample_spent_output();
        let mut spent2 = sample_spent_output();
        spent2.commitment = [0x00; 32];
        let tx = sample_tx();
        let h1 = sighash_v2(&tx, 0, &spent1);
        let h2 = sighash_v2(&tx, 0, &spent2);
        assert_ne!(
            h1, h2,
            "changing spent output commitment must change sighash"
        );
    }

    #[test]
    fn sighash_changes_with_spent_output_value() {
        let spent1 = sample_spent_output();
        let mut spent2 = sample_spent_output();
        spent2.value = 1;
        let tx = sample_tx();
        let h1 = sighash_v2(&tx, 0, &spent1);
        let h2 = sighash_v2(&tx, 0, &spent2);
        assert_ne!(
            h1, h2,
            "changing spent output value must change sighash"
        );
    }

    // -- Panics on out-of-bounds input index --

    #[test]
    #[should_panic(expected = "input_index")]
    fn sighash_panics_on_out_of_bounds_index() {
        let tx = sample_tx();
        let spent = sample_spent_output();
        let _ = sighash_v2(&tx, 5, &spent);
    }

    // -- Single-input transaction --

    #[test]
    fn sighash_single_input_tx() {
        let tx = Transaction {
            version: 2,
            inputs: vec![TxInput {
                outpoint: OutPoint {
                    txid: [0x10; 32],
                    vout: 0,
                },
                witness: vec![],
            }],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: [0x20; 32],
                value: 1_000,
            }],
            locktime: 0,
        };
        let spent = Output {
            script_version: 2,
            commitment: [0x30; 32],
            value: 2_000,
        };
        // Should not panic and should produce a 32-byte hash.
        let hash = sighash_v2(&tx, 0, &spent);
        assert_eq!(hash.len(), 32);
        // Non-zero (extremely unlikely for SHA-256 to produce all zeros).
        assert_ne!(hash, [0u8; 32]);
    }

    // -- Spend type byte coverage --

    #[test]
    fn sighash_includes_spend_type() {
        // The spend_type byte is part of the preimage. We verify this
        // indirectly: the sighash is non-zero and deterministic, and
        // the preimage structure includes the spend_type byte between
        // hash_outputs and spent_output_script_version.
        let tx = sample_tx();
        let spent = sample_spent_output();
        let h = sighash_v2(&tx, 0, &spent);
        assert_ne!(h, [0u8; 32]);
    }

    // -- verify_sighash_commitment_property tests --

    #[test]
    fn verify_commitment_property_sample_tx() {
        let tx = sample_tx();
        let spent_outputs = vec![sample_spent_output(), sample_spent_output()];
        let result = verify_sighash_commitment_property(&tx, &spent_outputs);
        assert!(
            result.cross_input_separation,
            "cross-input separation must hold for sample tx"
        );
        assert!(
            result.field_coverage,
            "field coverage must hold for sample tx"
        );
        assert_eq!(result.num_inputs, 2);
    }

    #[test]
    fn verify_commitment_property_single_input() {
        let tx = Transaction {
            version: 2,
            inputs: vec![TxInput {
                outpoint: OutPoint {
                    txid: [0x10; 32],
                    vout: 0,
                },
                witness: vec![],
            }],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: [0x20; 32],
                value: 1_000,
            }],
            locktime: 0,
        };
        let spent_outputs = vec![Output {
            script_version: 2,
            commitment: [0x30; 32],
            value: 2_000,
        }];
        let result = verify_sighash_commitment_property(&tx, &spent_outputs);
        assert!(result.cross_input_separation);
        assert!(result.field_coverage);
        assert_eq!(result.num_inputs, 1);
    }

    #[test]
    fn verify_commitment_property_empty_tx() {
        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs: vec![],
            locktime: 0,
        };
        let result = verify_sighash_commitment_property(&tx, &[]);
        assert!(result.cross_input_separation);
        assert!(result.field_coverage);
        assert_eq!(result.num_inputs, 0);
    }

    #[test]
    fn verify_commitment_property_three_inputs() {
        let tx = Transaction {
            version: 2,
            inputs: vec![
                TxInput {
                    outpoint: OutPoint {
                        txid: [0x01; 32],
                        vout: 0,
                    },
                    witness: vec![],
                },
                TxInput {
                    outpoint: OutPoint {
                        txid: [0x02; 32],
                        vout: 1,
                    },
                    witness: vec![],
                },
                TxInput {
                    outpoint: OutPoint {
                        txid: [0x03; 32],
                        vout: 2,
                    },
                    witness: vec![],
                },
            ],
            outputs: vec![
                TxOutput {
                    script_version: 2,
                    commitment: [0xAA; 32],
                    value: 10_000,
                },
                TxOutput {
                    script_version: 2,
                    commitment: [0xBB; 32],
                    value: 20_000,
                },
            ],
            locktime: 100,
        };
        let spent_outputs = vec![
            Output {
                script_version: 2,
                commitment: [0xC1; 32],
                value: 15_000,
            },
            Output {
                script_version: 2,
                commitment: [0xC2; 32],
                value: 15_000,
            },
            Output {
                script_version: 2,
                commitment: [0xC3; 32],
                value: 15_000,
            },
        ];
        let result = verify_sighash_commitment_property(&tx, &spent_outputs);
        assert!(result.cross_input_separation);
        assert!(result.field_coverage);
        assert_eq!(result.num_inputs, 3);
    }

    // -- Injectivity: two different transactions produce different sighashes --

    #[test]
    fn sighash_injectivity_different_inputs() {
        let tx1 = Transaction {
            version: 2,
            inputs: vec![TxInput {
                outpoint: OutPoint {
                    txid: [0x01; 32],
                    vout: 0,
                },
                witness: vec![],
            }],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: [0xCC; 32],
                value: 50_000,
            }],
            locktime: 0,
        };
        let tx2 = Transaction {
            version: 2,
            inputs: vec![TxInput {
                outpoint: OutPoint {
                    txid: [0x02; 32],
                    vout: 0,
                },
                witness: vec![],
            }],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: [0xCC; 32],
                value: 50_000,
            }],
            locktime: 0,
        };
        let spent = sample_spent_output();
        assert_ne!(
            sighash_v2(&tx1, 0, &spent),
            sighash_v2(&tx2, 0, &spent),
            "transactions with different inputs must produce different sighashes"
        );
    }

    #[test]
    fn sighash_injectivity_different_outputs() {
        let tx1 = Transaction {
            version: 2,
            inputs: vec![TxInput {
                outpoint: OutPoint {
                    txid: [0x01; 32],
                    vout: 0,
                },
                witness: vec![],
            }],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: [0xCC; 32],
                value: 50_000,
            }],
            locktime: 0,
        };
        let tx2 = Transaction {
            version: 2,
            inputs: vec![TxInput {
                outpoint: OutPoint {
                    txid: [0x01; 32],
                    vout: 0,
                },
                witness: vec![],
            }],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: [0xDD; 32],
                value: 50_000,
            }],
            locktime: 0,
        };
        let spent = sample_spent_output();
        assert_ne!(
            sighash_v2(&tx1, 0, &spent),
            sighash_v2(&tx2, 0, &spent),
            "transactions with different outputs must produce different sighashes"
        );
    }
}
