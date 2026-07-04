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
pub use types::{
    Block, Commitment, PubKey, ScriptType, Signature, Transaction, UtxoSet, UtxoStore,
};

// Encoding: witness serialization and parsing (Req 2.3, 6.5, 11.1–11.5)
pub use encoding::{
    is_canonical_consensus_witness, parse_consensus_witness, parse_multisig_witness, parse_witness,
    serialize_multisig_witness, serialize_witness,
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

#[cfg(kani)]
mod kani_proofs;

// ---------------------------------------------------------------------------
// Transaction validation and UTXO transitions (Task 11.1)
// ---------------------------------------------------------------------------

#[cfg(not(kani))]
use std::collections::HashSet;

#[cfg(not(kani))]
use sha2::{Digest, Sha256};

use crate::freeze::check_no_frozen_inputs;
use crate::types::{OutPoint, Output};

const TXID_PREIMAGE_DOMAIN: &[u8] = b"BitcoinPQ:txid:v1";

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
    #[cfg(not(kani))]
    {
        let mut seen = HashSet::with_capacity(tx.inputs.len());
        for input in &tx.inputs {
            if !seen.insert(&input.outpoint) {
                return false;
            }
        }
    }
    #[cfg(kani)]
    {
        for i in 0..tx.inputs.len() {
            for j in (i + 1)..tx.inputs.len() {
                if tx.inputs[i].outpoint == tx.inputs[j].outpoint {
                    return false;
                }
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
    delta_tx_remove_spent_outputs(utxo_set, tx);

    // Step 2: Compute a deterministic txid
    let txid = compute_txid(tx);

    // Step 3: Add new outpoints
    delta_tx_insert_created_outputs(utxo_set, tx, txid);
}

fn delta_tx_remove_spent_outputs(utxo_set: &mut UtxoSet, tx: &Transaction) {
    for input in &tx.inputs {
        utxo_set.remove(&input.outpoint);
    }
}

fn delta_tx_insert_created_outputs(utxo_set: &mut UtxoSet, tx: &Transaction, txid: [u8; 32]) {
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

/// Serialize the consensus-significant transaction fields committed by
/// `compute_txid`.
///
/// This is the protocol model's txid transcript, not Bitcoin's legacy txid
/// serialization. The domain tag and explicit input/output counts make the
/// transcript structurally self-delimiting before it is passed to SHA-256.
pub fn txid_preimage(tx: &Transaction) -> Vec<u8> {
    let capacity = TXID_PREIMAGE_DOMAIN.len()
        + 4
        + 8
        + tx.inputs.len() * (32 + 4)
        + 8
        + tx.outputs.len() * (1 + 32 + 8)
        + 4;
    let mut preimage = Vec::with_capacity(capacity);

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

/// Compute a deterministic transaction ID using SHA-256.
///
/// Hashes `txid_preimage(tx)`, i.e. a domain-separated transcript containing
/// version, input count, fixed-width input outpoints, output count, fixed-width
/// outputs, and locktime.
///
/// This is a simplified model txid — deterministic and collision-resistant
/// for our purposes, satisfying the txid collision-resistance assumption
/// (Definition 8 in the paper).
#[cfg(not(kani))]
pub fn compute_txid(tx: &Transaction) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(txid_preimage(tx));
    hasher.finalize().into()
}

/// Compute a deterministic transaction ID for Kani transition harnesses.
///
/// This is a bounded structural txid model, not SHA-256. It keeps `delta_tx`
/// and `valid_block` source-level verification focused on transition behavior
/// without pulling the cryptographic hash implementation into Kani. The runtime
/// implementation above remains SHA-256 based.
#[cfg(kani)]
pub fn compute_txid(tx: &Transaction) -> [u8; 32] {
    let mut txid = [0u8; 32];

    let version = tx.version.to_le_bytes();
    txid[0] = version[0];
    txid[1] = version[1];
    txid[2] = tx.inputs.len() as u8;
    txid[3] = tx.outputs.len() as u8;

    if let Some(input) = tx.inputs.first() {
        txid[4] = input.outpoint.txid[0];
        txid[5] = input.outpoint.txid[31];
        txid[6] = input.outpoint.vout as u8;
    }
    if let Some(input) = tx.inputs.get(1) {
        txid[8] = input.outpoint.txid[0];
        txid[9] = input.outpoint.txid[31];
        txid[10] = input.outpoint.vout as u8;
    }

    if let Some(output) = tx.outputs.first() {
        txid[20] = output.script_version;
        txid[21] = output.commitment[0];
        txid[22] = output.commitment[31];
        txid[23] = output.value as u8;
    }
    if let Some(output) = tx.outputs.get(1) {
        txid[24] = output.script_version;
        txid[25] = output.commitment[0];
        txid[26] = output.commitment[31];
        txid[27] = output.value as u8;
    }

    let locktime = tx.locktime.to_le_bytes();
    txid[30] = locktime[0];
    txid[31] ^= locktime[1];

    txid
}

/// Apply block transactions sequentially and return the resulting UTXO set.
///
/// This is the operational state transformer corresponding to the structural
/// Coq function `apply_block_transitions_structural`: every transaction is
/// validated against the evolving local UTXO set before its transition is
/// applied. The caller's UTXO set is never mutated.
pub fn apply_block_transitions(
    utxo_set: &UtxoSet,
    block: &Block,
    height: u64,
    config: &MigrationConfig,
) -> Option<UtxoSet> {
    let mut local_utxo = utxo_set.clone();

    for tx in block {
        if !valid_tx(&local_utxo, tx, height, config) {
            return None;
        }
        delta_tx(&mut local_utxo, tx);
    }

    Some(local_utxo)
}

/// Validate a block and return the final UTXO set when it is accepted.
///
/// This function is the operational counterpart of `valid_block`: acceptance is
/// equivalent to returning `Some(final_utxo)`. Keeping the final state explicit
/// makes PO-5 refinement check the state transition itself, not only the
/// accept/reject bit.
pub fn validate_and_apply_block(
    utxo_set: &UtxoSet,
    block: &Block,
    height: u64,
    config: &MigrationConfig,
) -> Option<UtxoSet> {
    let final_utxo = apply_block_transitions(utxo_set, block, height, config)?;

    if !check_block_cost(block) {
        return None;
    }

    Some(final_utxo)
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
    validate_and_apply_block(utxo_set, block, height, config).is_some()
}

// ---------------------------------------------------------------------------
// Unit tests for valid_tx, delta_tx, valid_block
// ---------------------------------------------------------------------------

#[cfg(test)]
mod validation_tests {
    use super::*;
    use crate::types::{OutPoint, Output, Transaction, TxInput, TxOutput};

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
    fn txid_preimage_is_domain_separated_and_self_delimiting() {
        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(outpoint(1)), tx_input(outpoint(2))],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 144,
        };

        let preimage = txid_preimage(&tx);

        assert!(preimage.starts_with(TXID_PREIMAGE_DOMAIN));
        let version_start = TXID_PREIMAGE_DOMAIN.len();
        assert_eq!(
            &preimage[version_start..version_start + 4],
            &2u32.to_le_bytes()
        );
        let input_count_start = version_start + 4;
        assert_eq!(
            &preimage[input_count_start..input_count_start + 8],
            &2u64.to_le_bytes()
        );
        let output_count_start = input_count_start + 8 + (2 * (32 + 4));
        assert_eq!(
            &preimage[output_count_start..output_count_start + 8],
            &1u64.to_le_bytes()
        );
        assert_eq!(&preimage[preimage.len() - 4..], &144u32.to_le_bytes());
    }

    #[test]
    fn compute_txid_hashes_the_txid_preimage() {
        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(outpoint(1))],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };

        let mut hasher = Sha256::new();
        hasher.update(txid_preimage(&tx));
        let expected: [u8; 32] = hasher.finalize().into();

        assert_eq!(compute_txid(&tx), expected);
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
    fn apply_block_transitions_returns_final_utxo_for_legacy_dependency() {
        let config = test_config();
        let root = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(root.clone(), legacy_utxo_output(100_000));

        let tx1 = Transaction {
            version: 2,
            inputs: vec![tx_input(root.clone())],
            outputs: vec![TxOutput {
                script_version: 0,
                commitment: [0xDD; 32],
                value: 100_000,
            }],
            locktime: 0,
        };
        let tx1_output = OutPoint {
            txid: compute_txid(&tx1),
            vout: 0,
        };
        let tx2 = Transaction {
            version: 2,
            inputs: vec![tx_input(tx1_output.clone())],
            outputs: vec![TxOutput {
                script_version: 0,
                commitment: [0xEE; 32],
                value: 90_000,
            }],
            locktime: 0,
        };
        let tx2_output = OutPoint {
            txid: compute_txid(&tx2),
            vout: 0,
        };
        let block = vec![tx1, tx2];

        let final_utxo = apply_block_transitions(&utxo_set, &block, 50_000, &config)
            .expect("sequential legacy dependency should be applied");

        assert!(!final_utxo.contains_key(&root));
        assert!(!final_utxo.contains_key(&tx1_output));
        let output = final_utxo
            .get(&tx2_output)
            .expect("second transaction output should exist");
        assert_eq!(output.script_version, 0);
        assert_eq!(output.value, 90_000);
        assert!(utxo_set.contains_key(&root));
    }

    #[test]
    fn validate_and_apply_block_is_valid_block_with_final_state() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_utxo_output(50_000));

        let valid = vec![Transaction {
            version: 2,
            inputs: vec![tx_input(op.clone())],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        }];
        assert_eq!(
            validate_and_apply_block(&utxo_set, &valid, 50_000, &config).is_some(),
            valid_block(&utxo_set, &valid, 50_000, &config)
        );

        let invalid = vec![Transaction {
            version: 2,
            inputs: vec![tx_input(outpoint(99))],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        }];
        assert_eq!(
            validate_and_apply_block(&utxo_set, &invalid, 50_000, &config).is_some(),
            valid_block(&utxo_set, &invalid, 50_000, &config)
        );
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
