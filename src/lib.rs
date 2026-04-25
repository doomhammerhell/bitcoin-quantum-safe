//! Bitcoin Post-Quantum Witness Protocol
//!
//! This crate implements a consensus-level post-quantum (PQ) witness protocol for Bitcoin,
//! introducing SegWit witness version 2 carrying ML-DSA-44 (FIPS 204) signatures, a
//! three-phase migration plan, and an explicit freeze policy for exposed/lost-key outputs.
//!
//! The design is grounded in the formal results of "Toward Protocol-Level Quantum Safety
//! in Bitcoin" (Giovani, 2026).

/// Core types: commitments, keys, transactions, UTXO set, witness/script enums.
pub mod types;

/// Varint and witness serialization/parsing (single-sig and multisig).
pub mod encoding;

/// SpendPred_PQ: post-quantum spend predicate (single-sig and multisig).
pub mod spend_pred;

/// Sighash v2 computation with PQ-specific domain separation.
pub mod sighash;

/// Migration_Controller: three-phase migration enforcement.
pub mod migration;

/// Weight_Accountant: cost function and block cost invariant.
pub mod weight;

/// Freeze_Enforcer: frozen output detection and spend rejection.
pub mod freeze;

/// Consensus parameters and constants.
pub mod params;

// ---------------------------------------------------------------------------
// Public API re-exports
// ---------------------------------------------------------------------------

// Types (Req 2.1, 2.2)
pub use types::{Block, Commitment, PubKey, ScriptType, Signature, Transaction, UtxoSet};

// Encoding: witness serialization and parsing (Req 2.3, 6.5, 11.1–11.5)
pub use encoding::{
    parse_multisig_witness, parse_witness, serialize_multisig_witness, serialize_witness,
};

// Spend predicates (Req 2.4–2.9, 6.2, 6.5, 6.6, 6.8)
pub use spend_pred::{spend_pred_pq, spend_pred_pq_multisig};

// Sighash v2 (Req 2.8, 10.2)
pub use sighash::{sighash_v2, tagged_hash, verify_sighash_commitment_property};

// Migration controller (Req 4.1–4.5, 4.9)
pub use migration::{check_migration_rules, MigrationPhase};

// Weight accountant (Req 3.1, 3.2, 8.1)
pub use weight::{check_block_cost, cost_tx};

// Freeze enforcer (Req 5.1, 5.2, 5.3)
pub use freeze::is_frozen;

// Consensus parameters (Req 1.1, 1.2, 1.5, 2.9, 3.5, 4.1, 4.6, 8.1)
pub use params::{
    MigrationConfig, ALPHA, COMMITMENT_LEN, C_MAX, MAX_WITNESS_SIZE, MIN_GRACE_PERIOD,
    ML_DSA_44_PK_LEN, ML_DSA_44_SIG_LEN, RECOMMENDED_GRACE_PERIOD, SLH_DSA_128S_PK_LEN,
    SLH_DSA_128S_SIG_LEN, WITNESS_VERSION,
};

#[cfg(test)]
mod tests;

// ---------------------------------------------------------------------------
// Transaction validation and UTXO transitions (Task 11.1)
// ---------------------------------------------------------------------------

use std::collections::HashSet;

use sha2::{Digest, Sha256};

use crate::freeze::check_no_frozen_inputs;
use crate::types::{OutPoint, Output};

/// Validate a transaction against the UTXO set and consensus rules.
///
/// Implements the `ValidTx(U, tx)` predicate from the design document.
/// Validation steps (in order):
///
/// 1. **No duplicate inputs:** reject if any outpoint appears more than once
///    in `tx.inputs`.
/// 2. **All inputs exist:** every input's outpoint must be present in the
///    UTXO set.
/// 3. **Value conservation:** the sum of input values (looked up from the
///    UTXO set) must be ≥ the sum of output values.
/// 4. **Migration rules:** `check_migration_rules(height, tx, utxo_set, config)`
///    must pass (phase-dependent output/spend restrictions).
/// 5. **Freeze check:** `check_no_frozen_inputs(height, tx, utxo_set, config)`
///    must pass (no spending of frozen legacy outputs after cutover).
/// 6. **Witness validation:** for each input spending a v2 (PQ) output,
///    compute the sighash and verify `SpendPred_PQ(commitment, sighash, witness)`.
///    Inputs spending non-v2 outputs are assumed valid (legacy validation is
///    outside the scope of this PQ protocol model).
///
/// # Requirements: 9.1, 9.2, 9.3
pub fn valid_tx(
    utxo_set: &UtxoSet,
    tx: &Transaction,
    height: u64,
    config: &MigrationConfig,
) -> bool {
    // Step 1: No duplicate inputs
    {
        let mut seen = HashSet::with_capacity(tx.inputs.len());
        for input in &tx.inputs {
            if !seen.insert(&input.outpoint) {
                return false;
            }
        }
    }

    // Step 2: All inputs exist in the UTXO set
    let input_outputs: Vec<&Output> = {
        let mut outputs = Vec::with_capacity(tx.inputs.len());
        for input in &tx.inputs {
            match utxo_set.get(&input.outpoint) {
                Some(output) => outputs.push(output),
                None => return false,
            }
        }
        outputs
    };

    // Step 3: Value conservation — sum(input values) >= sum(output values)
    {
        let input_sum: u64 = input_outputs.iter().map(|o| o.value).sum();
        let output_sum: u64 = tx.outputs.iter().map(|o| o.value).sum();
        if input_sum < output_sum {
            return false;
        }
    }

    // Step 4: Migration rules
    if !check_migration_rules(height, tx, utxo_set, config) {
        return false;
    }

    // Step 5: Freeze check
    if !check_no_frozen_inputs(height, tx, utxo_set, config) {
        return false;
    }

    // Step 6: Witness validation for v2 (PQ) inputs
    for (i, input) in tx.inputs.iter().enumerate() {
        let spent_output = input_outputs[i];
        if spent_output.script_version == 2 {
            let sighash = sighash_v2(tx, i, spent_output);
            if !spend_pred_pq(&spent_output.commitment, &sighash, &input.witness) {
                return false;
            }
        }
        // Non-v2 inputs: legacy validation is outside the scope of this model.
        // During the grace period, legacy spends are accepted by migration rules.
    }

    true
}

/// Apply a transaction to the UTXO set: remove spent outpoints, add new ones.
///
/// Implements the `DeltaTx(U, tx)` state transition from the design document.
///
/// 1. **Remove** all outpoints referenced by `tx.inputs` from the UTXO set.
/// 2. **Add** new outpoints: compute a deterministic txid (SHA-256 hash of
///    the transaction's key fields), then insert each output with the
///    computed txid and its index as `vout`.
///
/// The txid computation uses SHA-256 over `version || inputs || outputs || locktime`
/// for determinism and collision resistance. This is a simplified model — it
/// does not match Bitcoin's actual txid computation but satisfies the
/// collision-resistance assumption (Definition 8 in the paper).
///
/// # Requirements: 9.1, 9.2, 9.3
pub fn delta_tx(utxo_set: &mut UtxoSet, tx: &Transaction) {
    // Step 1: Remove spent outpoints
    for input in &tx.inputs {
        utxo_set.remove(&input.outpoint);
    }

    // Step 2: Compute a deterministic txid
    let txid = compute_txid(tx);

    // Step 3: Add new outpoints
    for (vout, output) in tx.outputs.iter().enumerate() {
        let outpoint = OutPoint {
            txid,
            vout: vout as u32,
        };
        let utxo_output = Output {
            script_version: output.script_version,
            commitment: output.commitment,
            value: output.value,
        };
        utxo_set.insert(outpoint, utxo_output);
    }
}

/// Compute a deterministic transaction ID using SHA-256.
///
/// Hashes: `version (4 LE) || for each input: txid (32) || vout (4 LE) ||
/// for each output: script_version (1) || commitment (32) || value (8 LE) ||
/// locktime (4 LE)`.
///
/// This is a simplified model txid — deterministic and collision-resistant
/// for our purposes, satisfying the txid collision-resistance assumption
/// (Definition 8 in the paper).
fn compute_txid(tx: &Transaction) -> [u8; 32] {
    let mut hasher = Sha256::new();

    hasher.update(tx.version.to_le_bytes());

    for input in &tx.inputs {
        hasher.update(input.outpoint.txid);
        hasher.update(input.outpoint.vout.to_le_bytes());
    }

    for output in &tx.outputs {
        hasher.update([output.script_version]);
        hasher.update(output.commitment);
        hasher.update(output.value.to_le_bytes());
    }

    hasher.update(tx.locktime.to_le_bytes());

    hasher.finalize().into()
}

/// Validate a block against the UTXO set and consensus rules.
///
/// Implements the `ValidBlk(U, B)` predicate from the design document:
///
/// 1. Clone the UTXO set to avoid mutating the caller's state on failure.
/// 2. For each transaction in the block:
///    a. Validate with `valid_tx` against the current (evolving) UTXO set.
///    b. Apply `delta_tx` to update the UTXO set for subsequent transactions.
/// 3. After all transactions: check the block cost invariant
///    (`check_block_cost(block)`).
/// 4. Return `true` only if all validations pass.
///
/// # Requirements: 9.1, 9.2, 9.3, 9.4
pub fn valid_block(
    utxo_set: &UtxoSet,
    block: &Block,
    height: u64,
    config: &MigrationConfig,
) -> bool {
    // Step 1: Clone the UTXO set for local mutation
    let mut local_utxo = utxo_set.clone();

    // Step 2: Validate and apply each transaction sequentially
    for tx in block {
        // Step 2a: Validate
        if !valid_tx(&local_utxo, tx, height, config) {
            return false;
        }
        // Step 2b: Apply state transition
        delta_tx(&mut local_utxo, tx);
    }

    // Step 3: Check block cost invariant
    if !check_block_cost(block) {
        return false;
    }

    true
}

// ---------------------------------------------------------------------------
// Unit tests for valid_tx, delta_tx, valid_block
// ---------------------------------------------------------------------------

#[cfg(test)]
mod validation_tests {
    use super::*;
    use crate::types::{OutPoint, Output, TxInput, TxOutput, Transaction};

    /// Helper: create a MigrationConfig with H_a=100_000 and recommended grace.
    fn test_config() -> MigrationConfig {
        MigrationConfig::with_recommended_grace(100_000)
    }

    /// Helper: create an outpoint with a given id byte.
    fn outpoint(id: u8) -> OutPoint {
        let mut txid = [0u8; 32];
        txid[0] = id;
        OutPoint { txid, vout: 0 }
    }

    /// Helper: create a legacy (v0) output for the UTXO set.
    fn legacy_utxo_output(value: u64) -> Output {
        Output {
            script_version: 0,
            commitment: [0xBB; 32],
            value,
        }
    }

    /// Helper: create a PQ (v2) transaction output.
    fn pq_tx_output(value: u64) -> TxOutput {
        TxOutput {
            script_version: 2,
            commitment: [0xCC; 32],
            value,
        }
    }

    /// Helper: create a transaction input with a dummy witness.
    fn tx_input(op: OutPoint) -> TxInput {
        TxInput {
            outpoint: op,
            witness: vec![0xDE, 0xAD],
        }
    }

    // -----------------------------------------------------------------------
    // valid_tx tests
    // -----------------------------------------------------------------------

    #[test]
    fn valid_tx_rejects_duplicate_inputs() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_utxo_output(100_000));

        // Transaction with the same input twice
        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op.clone()), tx_input(op)],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };

        // Pre-activation: legacy spends allowed, but duplicate inputs rejected
        assert!(!valid_tx(&utxo_set, &tx, 50_000, &config));
    }

    #[test]
    fn valid_tx_rejects_missing_input() {
        let config = test_config();
        let op = outpoint(99); // not in UTXO set
        let utxo_set = UtxoSet::new();

        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };

        assert!(!valid_tx(&utxo_set, &tx, 50_000, &config));
    }

    #[test]
    fn valid_tx_rejects_value_inflation() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_utxo_output(50_000));

        // Output value exceeds input value
        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![pq_tx_output(100_000)],
            locktime: 0,
        };

        assert!(!valid_tx(&utxo_set, &tx, 50_000, &config));
    }

    #[test]
    fn valid_tx_accepts_value_conservation_with_fee() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_utxo_output(100_000));

        // Output value < input value (difference is the fee)
        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![pq_tx_output(90_000)],
            locktime: 0,
        };

        // Pre-activation: legacy spends allowed
        assert!(valid_tx(&utxo_set, &tx, 50_000, &config));
    }

    #[test]
    fn valid_tx_accepts_exact_value_conservation() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_utxo_output(50_000));

        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };

        assert!(valid_tx(&utxo_set, &tx, 50_000, &config));
    }

    #[test]
    fn valid_tx_rejects_legacy_output_creation_after_ha() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_utxo_output(50_000));

        // Create a legacy output after H_a
        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![TxOutput {
                script_version: 0,
                commitment: [0xDD; 32],
                value: 50_000,
            }],
            locktime: 0,
        };

        assert!(!valid_tx(&utxo_set, &tx, 100_000, &config));
    }

    #[test]
    fn valid_tx_rejects_frozen_input_after_cutover() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_utxo_output(50_000));

        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };

        // After cutover: legacy inputs are frozen
        assert!(!valid_tx(&utxo_set, &tx, 152_560, &config));
    }

    #[test]
    fn valid_tx_accepts_legacy_spend_during_grace_period() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_utxo_output(50_000));

        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };

        // During grace period: legacy spends allowed with PQ outputs
        assert!(valid_tx(&utxo_set, &tx, 120_000, &config));
    }

    #[test]
    fn valid_tx_empty_transaction() {
        let config = test_config();
        let utxo_set = UtxoSet::new();

        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs: vec![],
            locktime: 0,
        };

        // Empty transaction: no inputs to check, value conservation holds (0 >= 0)
        assert!(valid_tx(&utxo_set, &tx, 50_000, &config));
    }

    // -----------------------------------------------------------------------
    // delta_tx tests
    // -----------------------------------------------------------------------

    #[test]
    fn delta_tx_removes_spent_outpoints() {
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_utxo_output(50_000));

        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op.clone())],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };

        delta_tx(&mut utxo_set, &tx);

        // The spent outpoint should be removed
        assert!(!utxo_set.contains_key(&op));
    }

    #[test]
    fn delta_tx_adds_new_outpoints() {
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_utxo_output(50_000));

        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![pq_tx_output(30_000), pq_tx_output(20_000)],
            locktime: 0,
        };

        let initial_size = utxo_set.len();
        delta_tx(&mut utxo_set, &tx);

        // 1 removed, 2 added → net +1
        assert_eq!(utxo_set.len(), initial_size - 1 + 2);

        // Verify the new outpoints exist with correct values
        let txid = compute_txid(&tx);
        let new_op0 = OutPoint { txid, vout: 0 };
        let new_op1 = OutPoint { txid, vout: 1 };

        let out0 = utxo_set.get(&new_op0).expect("output 0 should exist");
        assert_eq!(out0.value, 30_000);
        assert_eq!(out0.script_version, 2);

        let out1 = utxo_set.get(&new_op1).expect("output 1 should exist");
        assert_eq!(out1.value, 20_000);
        assert_eq!(out1.script_version, 2);
    }

    #[test]
    fn delta_tx_empty_transaction() {
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(outpoint(1), legacy_utxo_output(50_000));

        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs: vec![],
            locktime: 0,
        };

        let size_before = utxo_set.len();
        delta_tx(&mut utxo_set, &tx);
        assert_eq!(utxo_set.len(), size_before);
    }

    #[test]
    fn compute_txid_is_deterministic() {
        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(outpoint(1))],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };

        let id1 = compute_txid(&tx);
        let id2 = compute_txid(&tx);
        assert_eq!(id1, id2);
    }

    #[test]
    fn compute_txid_different_for_different_txs() {
        let tx1 = Transaction {
            version: 2,
            inputs: vec![tx_input(outpoint(1))],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };

        let tx2 = Transaction {
            version: 2,
            inputs: vec![tx_input(outpoint(2))],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };

        assert_ne!(compute_txid(&tx1), compute_txid(&tx2));
    }

    // -----------------------------------------------------------------------
    // valid_block tests
    // -----------------------------------------------------------------------

    #[test]
    fn valid_block_empty_block() {
        let config = test_config();
        let utxo_set = UtxoSet::new();
        let block: Block = vec![];

        assert!(valid_block(&utxo_set, &block, 50_000, &config));
    }

    #[test]
    fn valid_block_single_valid_tx() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_utxo_output(50_000));

        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };

        let block = vec![tx];
        // Pre-activation: legacy spends allowed
        assert!(valid_block(&utxo_set, &block, 50_000, &config));
    }

    #[test]
    fn valid_block_rejects_invalid_tx() {
        let config = test_config();
        let utxo_set = UtxoSet::new();

        // Transaction with missing input
        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(outpoint(99))],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };

        let block = vec![tx];
        assert!(!valid_block(&utxo_set, &block, 50_000, &config));
    }

    #[test]
    fn valid_block_sequential_tx_dependency() {
        let config = test_config();
        let op1 = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op1.clone(), legacy_utxo_output(100_000));

        // First tx: spend op1, create a new output
        let tx1 = Transaction {
            version: 2,
            inputs: vec![tx_input(op1)],
            outputs: vec![pq_tx_output(100_000)],
            locktime: 0,
        };

        // Second tx: spend the output created by tx1
        let tx1_id = compute_txid(&tx1);
        let op2 = OutPoint {
            txid: tx1_id,
            vout: 0,
        };
        let tx2 = Transaction {
            version: 2,
            inputs: vec![TxInput {
                outpoint: op2,
                witness: vec![0xDE, 0xAD],
            }],
            outputs: vec![pq_tx_output(100_000)],
            locktime: 0,
        };

        let block = vec![tx1, tx2];
        // Pre-activation: legacy spends allowed, tx2 spends tx1's PQ output
        // (witness validation for v2 will fail with dummy witness, but the
        // second tx spends a v2 output so it needs a valid PQ witness)
        // Since we use a dummy witness, this will fail at witness validation.
        // Let's test with pre-activation where the first tx creates a legacy output
        // that the second tx can spend without PQ witness validation.

        // Actually, let's just test that the block rejects because the second
        // tx has an invalid PQ witness for the v2 output.
        assert!(!valid_block(&utxo_set, &block, 50_000, &config));
    }

    #[test]
    fn valid_block_sequential_legacy_dependency() {
        let config = test_config();
        let op1 = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op1.clone(), legacy_utxo_output(100_000));

        // First tx: spend legacy op1, create a legacy output (pre-activation)
        let tx1 = Transaction {
            version: 2,
            inputs: vec![tx_input(op1)],
            outputs: vec![TxOutput {
                script_version: 0,
                commitment: [0xDD; 32],
                value: 100_000,
            }],
            locktime: 0,
        };

        // Second tx: spend the legacy output created by tx1
        let tx1_id = compute_txid(&tx1);
        let op2 = OutPoint {
            txid: tx1_id,
            vout: 0,
        };
        let tx2 = Transaction {
            version: 2,
            inputs: vec![TxInput {
                outpoint: op2,
                witness: vec![0xDE, 0xAD],
            }],
            outputs: vec![TxOutput {
                script_version: 0,
                commitment: [0xEE; 32],
                value: 100_000,
            }],
            locktime: 0,
        };

        let block = vec![tx1, tx2];
        // Pre-activation: legacy spends and outputs allowed, no PQ witness needed
        assert!(valid_block(&utxo_set, &block, 50_000, &config));
    }

    #[test]
    fn valid_block_does_not_mutate_original_utxo_set() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_utxo_output(50_000));

        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op.clone())],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };

        let block = vec![tx];
        let _ = valid_block(&utxo_set, &block, 50_000, &config);

        // Original UTXO set should be unchanged
        assert!(utxo_set.contains_key(&op));
        assert_eq!(utxo_set.len(), 1);
    }
}
