//! Migration_Controller: three-phase migration enforcement.
//!
//! Enforces phase-dependent rules on output creation and spending:
//! - Pre-activation (h < H_a): all output types allowed
//! - Grace period [H_a, H_c): PQ outputs only, legacy spends allowed
//! - Post-cutover (h ≥ H_c): PQ outputs only, PQ spends only
//!
//! Matches the TLA+ specification in `formal/tla/BitcoinPQ.tla`.

use crate::params::MigrationConfig;
use crate::types::{ScriptType, Transaction, UtxoSet};

// ---------------------------------------------------------------------------
// Migration phase
// ---------------------------------------------------------------------------

/// The three migration phases from the TLA+ specification.
///
/// The protocol transitions through these phases based on block height
/// relative to the announcement height (H_a) and cutover height (H_c).
///
/// Requirements: 4.1, 4.2
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MigrationPhase {
    /// Before activation (h < H_a): all output types and spend types allowed.
    PreActivation,
    /// Grace period [H_a, H_c): PQ outputs only, legacy spends still allowed.
    GracePeriod,
    /// Post-cutover (h ≥ H_c): PQ outputs only, PQ spends only.
    PostCutover,
}

// ---------------------------------------------------------------------------
// Phase determination
// ---------------------------------------------------------------------------

/// Determine the current migration phase for a given block height.
///
/// - `height < config.announcement_height` → `PreActivation`
/// - `config.announcement_height <= height < config.cutover_height` → `GracePeriod`
/// - `height >= config.cutover_height` → `PostCutover`
///
/// Requirements: 4.1, 4.2
pub fn get_phase(height: u64, config: &MigrationConfig) -> MigrationPhase {
    if height < config.announcement_height {
        MigrationPhase::PreActivation
    } else if height < config.cutover_height {
        MigrationPhase::GracePeriod
    } else {
        MigrationPhase::PostCutover
    }
}

// ---------------------------------------------------------------------------
// Migration rule enforcement
// ---------------------------------------------------------------------------

/// Check whether a transaction satisfies the migration rules at the given height.
///
/// Implements the `CheckMigrationRules` pseudocode from the design document:
///
/// ```text
/// function CheckMigrationRules(height, tx):
///     // After announcement: no new legacy outputs
///     if height >= H_a:
///         for each output o in tx.outputs:
///             if o.script is legacy type (P2PKH, P2WPKH, P2SH, P2WSH, P2TR-EC):
///                 return false
///
///     // After cutover: no legacy spend predicates
///     if height >= H_c:
///         for each input (op_i, w_i) in tx.inputs:
///             if UTXO[op_i].script.version != 2:  // not PQ-locked
///                 return false  // frozen output or legacy spend rejected
///
///     return true
/// ```
///
/// Requirements: 4.1, 4.2, 4.3, 4.4, 4.5, 4.9
pub fn check_migration_rules(
    height: u64,
    tx: &Transaction,
    utxo_set: &UtxoSet,
    config: &MigrationConfig,
) -> bool {
    // After announcement (h >= H_a): reject any transaction creating legacy outputs.
    // This enforces migration monotonicity (Proposition 4 in the paper):
    // the PQ fraction ρ(U_t) can only increase after H_a.
    if height >= config.announcement_height {
        for output in &tx.outputs {
            let script_type = ScriptType::from(output);
            if script_type.is_legacy() {
                return false;
            }
        }
    }

    // After cutover (h >= H_c): reject any input spending a non-PQ output.
    // This enforces SpendPred ≡ SpendPred_PQ for all inputs (Req 4.5)
    // and implements the freeze policy for unmigrated legacy outputs (Req 4.9, 5.1).
    if height >= config.cutover_height {
        for input in &tx.inputs {
            // If the outpoint is not in the UTXO set, this is an invalid
            // transaction (inputs don't exist), but that check belongs to
            // the broader ValidTx function. Here we only enforce migration
            // rules, so we skip missing outpoints.
            if let Some(utxo_entry) = utxo_set.get(&input.outpoint) {
                if utxo_entry.script_version != 2 {
                    return false;
                }
            }
        }
    }

    true
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{OutPoint, Output, TxInput, TxOutput};

    /// Helper: create a MigrationConfig with H_a=100_000, H_c=152_560
    /// (recommended ~1 year grace period).
    fn test_config() -> MigrationConfig {
        MigrationConfig::with_recommended_grace(100_000)
    }

    /// Helper: create a PQ (v2) output for the UTXO set.
    fn pq_utxo_output(value: u64) -> Output {
        Output {
            script_version: 2,
            commitment: [0xAA; 32],
            value,
        }
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

    /// Helper: create a legacy (v0) transaction output.
    fn legacy_tx_output(value: u64) -> TxOutput {
        TxOutput {
            script_version: 0,
            commitment: [0xDD; 32],
            value,
        }
    }

    /// Helper: create an outpoint with a given id.
    fn outpoint(id: u8) -> OutPoint {
        let mut txid = [0u8; 32];
        txid[0] = id;
        OutPoint { txid, vout: 0 }
    }

    /// Helper: create a transaction input referencing a given outpoint.
    fn tx_input(op: OutPoint) -> TxInput {
        TxInput {
            outpoint: op,
            witness: vec![0xDE, 0xAD],
        }
    }

    // -- get_phase tests --

    #[test]
    fn phase_pre_activation_before_ha() {
        let config = test_config();
        assert_eq!(get_phase(0, &config), MigrationPhase::PreActivation);
        assert_eq!(get_phase(99_999, &config), MigrationPhase::PreActivation);
    }

    #[test]
    fn phase_grace_period_at_ha() {
        let config = test_config();
        assert_eq!(get_phase(100_000, &config), MigrationPhase::GracePeriod);
    }

    #[test]
    fn phase_grace_period_between_ha_and_hc() {
        let config = test_config();
        assert_eq!(get_phase(120_000, &config), MigrationPhase::GracePeriod);
        assert_eq!(get_phase(152_559, &config), MigrationPhase::GracePeriod);
    }

    #[test]
    fn phase_post_cutover_at_hc() {
        let config = test_config();
        assert_eq!(get_phase(152_560, &config), MigrationPhase::PostCutover);
    }

    #[test]
    fn phase_post_cutover_after_hc() {
        let config = test_config();
        assert_eq!(get_phase(200_000, &config), MigrationPhase::PostCutover);
    }

    // -- check_migration_rules: PreActivation phase --

    #[test]
    fn pre_activation_allows_legacy_outputs() {
        let config = test_config();
        let utxo_set = UtxoSet::new();
        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs: vec![legacy_tx_output(50_000)],
            locktime: 0,
        };
        assert!(check_migration_rules(99_999, &tx, &utxo_set, &config));
    }

    #[test]
    fn pre_activation_allows_pq_outputs() {
        let config = test_config();
        let utxo_set = UtxoSet::new();
        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };
        assert!(check_migration_rules(99_999, &tx, &utxo_set, &config));
    }

    #[test]
    fn pre_activation_allows_mixed_outputs() {
        let config = test_config();
        let utxo_set = UtxoSet::new();
        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs: vec![legacy_tx_output(25_000), pq_tx_output(25_000)],
            locktime: 0,
        };
        assert!(check_migration_rules(99_999, &tx, &utxo_set, &config));
    }

    // -- check_migration_rules: GracePeriod phase --

    #[test]
    fn grace_period_rejects_legacy_output_creation() {
        let config = test_config();
        let utxo_set = UtxoSet::new();
        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs: vec![legacy_tx_output(50_000)],
            locktime: 0,
        };
        // At exactly H_a: legacy creation rejected
        assert!(!check_migration_rules(100_000, &tx, &utxo_set, &config));
        // During grace period: legacy creation rejected
        assert!(!check_migration_rules(120_000, &tx, &utxo_set, &config));
    }

    #[test]
    fn grace_period_allows_pq_output_creation() {
        let config = test_config();
        let utxo_set = UtxoSet::new();
        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };
        assert!(check_migration_rules(100_000, &tx, &utxo_set, &config));
        assert!(check_migration_rules(120_000, &tx, &utxo_set, &config));
    }

    #[test]
    fn grace_period_allows_legacy_spends() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_utxo_output(50_000));

        // Spend legacy input, create PQ output (migration tx)
        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };
        assert!(check_migration_rules(100_000, &tx, &utxo_set, &config));
        assert!(check_migration_rules(152_559, &tx, &utxo_set, &config));
    }

    #[test]
    fn grace_period_rejects_legacy_output_even_with_legacy_spend() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), legacy_utxo_output(50_000));

        // Spend legacy input but create legacy output — rejected
        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![legacy_tx_output(50_000)],
            locktime: 0,
        };
        assert!(!check_migration_rules(100_000, &tx, &utxo_set, &config));
    }

    // -- check_migration_rules: PostCutover phase --

    #[test]
    fn post_cutover_rejects_legacy_spends() {
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
        // At exactly H_c: legacy spends rejected
        assert!(!check_migration_rules(152_560, &tx, &utxo_set, &config));
        // After H_c: legacy spends rejected
        assert!(!check_migration_rules(200_000, &tx, &utxo_set, &config));
    }

    #[test]
    fn post_cutover_allows_pq_spends() {
        let config = test_config();
        let op = outpoint(1);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op.clone(), pq_utxo_output(50_000));

        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op)],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };
        assert!(check_migration_rules(152_560, &tx, &utxo_set, &config));
        assert!(check_migration_rules(200_000, &tx, &utxo_set, &config));
    }

    #[test]
    fn post_cutover_rejects_legacy_output_creation() {
        let config = test_config();
        let utxo_set = UtxoSet::new();
        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs: vec![legacy_tx_output(50_000)],
            locktime: 0,
        };
        assert!(!check_migration_rules(152_560, &tx, &utxo_set, &config));
    }

    #[test]
    fn post_cutover_rejects_mixed_inputs_with_legacy() {
        let config = test_config();
        let op_legacy = outpoint(1);
        let op_pq = outpoint(2);
        let mut utxo_set = UtxoSet::new();
        utxo_set.insert(op_legacy.clone(), legacy_utxo_output(25_000));
        utxo_set.insert(op_pq.clone(), pq_utxo_output(25_000));

        // One PQ input + one legacy input → rejected after cutover
        let tx = Transaction {
            version: 2,
            inputs: vec![tx_input(op_pq), tx_input(op_legacy)],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };
        assert!(!check_migration_rules(152_560, &tx, &utxo_set, &config));
    }

    // -- Boundary tests --

    #[test]
    fn boundary_ha_minus_one_allows_legacy_creation() {
        let config = test_config();
        let utxo_set = UtxoSet::new();
        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs: vec![legacy_tx_output(50_000)],
            locktime: 0,
        };
        // H_a - 1: still pre-activation, legacy allowed
        assert!(check_migration_rules(99_999, &tx, &utxo_set, &config));
    }

    #[test]
    fn boundary_exactly_ha_rejects_legacy_creation() {
        let config = test_config();
        let utxo_set = UtxoSet::new();
        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs: vec![legacy_tx_output(50_000)],
            locktime: 0,
        };
        // Exactly H_a: legacy creation rejected
        assert!(!check_migration_rules(100_000, &tx, &utxo_set, &config));
    }

    #[test]
    fn boundary_hc_minus_one_allows_legacy_spends() {
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
        // H_c - 1: still grace period, legacy spends allowed
        assert!(check_migration_rules(152_559, &tx, &utxo_set, &config));
    }

    #[test]
    fn boundary_exactly_hc_rejects_legacy_spends() {
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
        // Exactly H_c: legacy spends rejected
        assert!(!check_migration_rules(152_560, &tx, &utxo_set, &config));
    }

    // -- PQ output creation allowed in all phases --

    #[test]
    fn pq_output_creation_allowed_in_all_phases() {
        let config = test_config();
        let utxo_set = UtxoSet::new();
        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs: vec![pq_tx_output(50_000)],
            locktime: 0,
        };
        // Pre-activation
        assert!(check_migration_rules(0, &tx, &utxo_set, &config));
        // Grace period
        assert!(check_migration_rules(100_000, &tx, &utxo_set, &config));
        // Post-cutover
        assert!(check_migration_rules(152_560, &tx, &utxo_set, &config));
    }

    // -- Frozen output becomes unspendable at H_c --

    #[test]
    fn unmigrated_legacy_output_frozen_at_cutover() {
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

        // During grace period: spendable
        assert!(check_migration_rules(152_559, &tx, &utxo_set, &config));
        // At cutover: frozen (spending rejected)
        assert!(!check_migration_rules(152_560, &tx, &utxo_set, &config));
    }

    // -- Various legacy script versions --

    #[test]
    fn post_cutover_rejects_all_legacy_script_versions() {
        let config = test_config();

        // Test script versions 0 (SegWit v0), 1 (Taproot), 3 (unknown/legacy bucket)
        for version in [0u8, 1, 3, 255] {
            let op = outpoint(version);
            let mut utxo_set = UtxoSet::new();
            utxo_set.insert(
                op.clone(),
                Output {
                    script_version: version,
                    commitment: [0; 32],
                    value: 50_000,
                },
            );

            let tx = Transaction {
                version: 2,
                inputs: vec![tx_input(op)],
                outputs: vec![pq_tx_output(50_000)],
                locktime: 0,
            };
            assert!(
                !check_migration_rules(152_560, &tx, &utxo_set, &config),
                "script_version {} should be rejected after cutover",
                version
            );
        }
    }

    // -- Empty transaction edge cases --

    #[test]
    fn empty_transaction_passes_all_phases() {
        let config = test_config();
        let utxo_set = UtxoSet::new();
        let tx = Transaction {
            version: 2,
            inputs: vec![],
            outputs: vec![],
            locktime: 0,
        };
        assert!(check_migration_rules(0, &tx, &utxo_set, &config));
        assert!(check_migration_rules(100_000, &tx, &utxo_set, &config));
        assert!(check_migration_rules(152_560, &tx, &utxo_set, &config));
    }
}
