//! Freeze_Enforcer: frozen output detection and spend rejection.
//!
//! Marks unmigrated legacy outputs as frozen (unspendable) at cutover height H_c.
//! Frozen outputs remain in the UTXO set (not pruned) to preserve the
//! StateConsistency invariant. Choosing safety over liveness per Theorem 9.
//!
//! Requirements: 5.1, 5.2, 5.3

use crate::params::MigrationConfig;
use crate::types::{Output, Transaction, UtxoSet};

// ---------------------------------------------------------------------------
// Frozen output detection
// ---------------------------------------------------------------------------

/// Check whether an output is frozen at the given block height.
///
/// An output is frozen if:
/// 1. The block height is at or past the cutover height H_c, AND
/// 2. The output's script version is not 2 (i.e., it is not a PQ-locked output).
///
/// Before H_c, no outputs are frozen regardless of their script version.
/// After H_c, all non-PQ outputs are frozen — they remain in the UTXO set
/// but are unspendable.
///
/// The freeze is implicit in the consensus rule: no explicit "freeze flag" is
/// set on outputs. The freeze status is deterministic, depending only on the
/// block height and the output's script version.
///
/// Requirements: 5.1, 5.2
pub fn is_frozen(height: u64, output: &Output, config: &MigrationConfig) -> bool {
    if height < config.cutover_height {
        return false;
    }
    output.script_version != 2
}

// ---------------------------------------------------------------------------
// Frozen input rejection
// ---------------------------------------------------------------------------

/// Check that no inputs of a transaction reference frozen outputs.
///
/// For each input in the transaction, looks up the corresponding output in
/// the UTXO set. If any referenced output is frozen (per [`is_frozen`]),
/// returns `false` — the transaction is invalid.
///
/// If an input's outpoint is not found in the UTXO set, it is skipped here
/// (the broader `ValidTx` function handles missing inputs). This function
/// only enforces the freeze policy.
///
/// Frozen outputs remain in the UTXO set — this function only checks,
/// never removes outputs.
///
/// Requirements: 5.2, 5.3
pub fn check_no_frozen_inputs(
    height: u64,
    tx: &Transaction,
    utxo_set: &UtxoSet,
    config: &MigrationConfig,
) -> bool {
    for input in &tx.inputs {
        if let Some(output) = utxo_set.get(&input.outpoint) {
            if is_frozen(height, output, config) {
                return false;
            }
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Unit tests (Task 9.3)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::params::MigrationConfig;
    use crate::types::{OutPoint, Output, TxInput, TxOutput, Transaction, UtxoSet};

    /// Helper: create a MigrationConfig with H_a=100_000, H_c=152_560
    /// (recommended ~1 year grace period).
    fn test_config() -> MigrationConfig {
        MigrationConfig::with_recommended_grace(100_000)
    }

    /// Helper: create an outpoint with a given id byte.
    fn outpoint(id: u8) -> OutPoint {
        let mut txid = [0u8; 32];
        txid[0] = id;
        OutPoint { txid, vout: 0 }
    }

    /// Helper: create a legacy (v0) output.
    fn legacy_output(value: u64) -> Output {
        Output {
            script_version: 0,
            commitment: [0xBB; 32],
            value,
        }
    }

    /// Helper: create a PQ (v2) output.
    fn pq_output(value: u64) -> Output {
        Output {
            script_version: 2,
            commitment: [0xAA; 32],
            value,
        }
    }

    /// Helper: create a Taproot (v1) output.
    fn taproot_output(value: u64) -> Output {
        Output {
            script_version: 1,
            commitment: [0xCC; 32],
            value,
        }
    }

    /// Helper: create a transaction input referencing a given outpoint.
    fn tx_input(op: OutPoint) -> TxInput {
        TxInput {
            outpoint: op,
            witness: vec![0xDE, 0xAD],
        }
    }

    // -- is_frozen: returns false for all outputs when height < H_c --

    #[test]
    fn is_frozen_returns_false_before_cutover_for_legacy() {
        let config = test_config();
        let output = legacy_output(50_000);

        // Well before cutover
        assert!(!is_frozen(0, &output, &config));
        assert!(!is_frozen(100_000, &output, &config)); // at H_a
        assert!(!is_frozen(152_559, &output, &config)); // H_c - 1
    }

    #[test]
    fn is_frozen_returns_false_before_cutover_for_pq() {
        let config = test_config();
        let output = pq_output(50_000);

        assert!(!is_frozen(0, &output, &config));
        assert!(!is_frozen(100_000, &output, &config));
        assert!(!is_frozen(152_559, &output, &config));
    }

    #[test]
    fn is_frozen_returns_false_before_cutover_for_taproot() {
        let config = test_config();
        let output = taproot_output(50_000);

        assert!(!is_frozen(0, &output, &config));
        assert!(!is_frozen(152_559, &output, &config));
    }

    // -- is_frozen: returns true for legacy outputs when height >= H_c --

    #[test]
    fn is_frozen_returns_true_for_legacy_at_cutover() {
        let config = test_config();
        let output = legacy_output(50_000);

        // Exactly at H_c
        assert!(is_frozen(152_560, &output, &config));
        // After H_c
        assert!(is_frozen(200_000, &output, &config));
    }

    #[test]
    fn is_frozen_returns_true_for_taproot_at_cutover() {
        let config = test_config();
        let output = taproot_output(50_000);

        assert!(is_frozen(152_560, &output, &config));
        assert!(is_frozen(200_000, &output, &config));
    }

    #[test]
    fn is_frozen_returns_true_for_all_legacy_versions_at_cutover() {
        let config = test_config();

        // Test all non-PQ script versions
        for version in [0u8, 1, 3, 4, 255] {
            let output = Output {
                script_version: version,
                commitment: [0; 32],
                value: 50_000,
            };
            assert!(
                is_frozen(152_560, &output, &config),
                "script_version {} should be frozen at cutover",
                version
            );
        }
    }

    // -- is_frozen: returns false for PQ (v2) outputs when height >= H_c --

    #[test]
    fn is_frozen_returns_false_for_pq_at_cutover() {
        let config = test_config();
        let output = pq_output(50_000);

        // PQ outputs are never frozen
        assert!(!is_frozen(152_560, &output, &config));
        assert!(!is_frozen(200_000, &output, &config));
        assert!(!is_frozen(u64::MAX, &output, &config));
    }

    // -- check_no_frozen_inputs: frozen output spend attempt is rejected --

    #[test]
    fn frozen_output_spend_rejected() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_output(50_000));

        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: [0xCC; 32],
                value: 50_000,
            }],
            locktime: 0,
        };

        // Before cutover: not frozen, spend allowed
        assert!(check_no_frozen_inputs(152_559, &tx, &utxo_set, &config));

        // At cutover: frozen, spend rejected
        assert!(!check_no_frozen_inputs(152_560, &tx, &utxo_set, &config));

        // After cutover: still frozen
        assert!(!check_no_frozen_inputs(200_000, &tx, &utxo_set, &config));
    }

    #[test]
    fn pq_output_spend_allowed_after_cutover() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), pq_output(50_000));

        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: [0xCC; 32],
                value: 50_000,
            }],
            locktime: 0,
        };

        // PQ outputs are never frozen — spend always allowed
        assert!(check_no_frozen_inputs(152_560, &tx, &utxo_set, &config));
        assert!(check_no_frozen_inputs(200_000, &tx, &utxo_set, &config));
    }

    #[test]
    fn mixed_inputs_rejected_if_any_frozen() {
        let config = test_config();
        let op_pq = outpoint(1);
        let op_legacy = outpoint(2);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op_pq.clone(), pq_output(25_000));
        utxo_set.insert(op_legacy.clone(), legacy_output(25_000));

        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op_pq), tx_input(op_legacy)],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: [0xCC; 32],
                value: 50_000,
            }],
            locktime: 0,
        };

        // One frozen input is enough to reject
        assert!(!check_no_frozen_inputs(152_560, &tx, &utxo_set, &config));
    }

    #[test]
    fn missing_utxo_does_not_cause_rejection() {
        let config = test_config();
        let op = outpoint(99); // not in UTXO set
        let utxo_set = UtxoSet::new();

        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: [0xCC; 32],
                value: 50_000,
            }],
            locktime: 0,
        };

        // Missing outpoints are skipped (ValidTx handles that check)
        assert!(check_no_frozen_inputs(152_560, &tx, &utxo_set, &config));
    }

    #[test]
    fn empty_transaction_passes_freeze_check() {
        let config = test_config();
        let utxo_set = UtxoSet::new();

        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs: vec![],
            locktime: 0,
        };

        assert!(check_no_frozen_inputs(152_560, &tx, &utxo_set, &config));
    }

    // -- Exchange freeze scenario (Req 12.5) --

    #[test]
    fn exchange_freeze_scenario() {
        let config = test_config();

        // Exchange holds multiple legacy outputs (simulating cold storage)
        let mut utxo_set = UtxoSet::new();
        let exchange_ops: Vec<OutPoint> = (1..=5).map(outpoint).collect();
        for op in &exchange_ops {
            utxo_set.insert(op.clone(), legacy_output(100_000));
        }

        // During grace period: exchange can spend legacy outputs (migrate)
        let migrate_tx = Transaction {
            version: 2,
            inputs: vec![tx_input(exchange_ops[0].clone())],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: [0xCC; 32],
                value: 100_000,
            }],
            locktime: 0,
        };
        assert!(check_no_frozen_inputs(152_559, &migrate_tx, &utxo_set, &config));

        // At cutover: all remaining legacy outputs become frozen
        for op in &exchange_ops {
            let output = utxo_set.get(op).unwrap();
            assert!(
                is_frozen(152_560, output, &config),
                "exchange legacy output should be frozen at cutover"
            );
        }

        // Exchange cannot spend any frozen output after cutover
        let spend_tx = Transaction {
            version: 2,
            inputs: vec![tx_input(exchange_ops[1].clone())],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: [0xCC; 32],
                value: 100_000,
            }],
            locktime: 0,
        };
        assert!(!check_no_frozen_inputs(152_560, &spend_tx, &utxo_set, &config));

        // Frozen outputs remain in the UTXO set (not removed)
        for op in &exchange_ops {
            assert!(
                utxo_set.contains_key(op),
                "frozen output must remain in UTXO set"
            );
        }
    }
}
