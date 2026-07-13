//! Structural transition-kernel adapter boundary for PO-5.
//!
//! This module intentionally does not introduce a second consensus semantics.
//! It isolates the deployed structural UTXO transition surface behind a small
//! contract so a future Coq-extracted transition core can replace the deployed
//! Rust adapter without changing callers.

use crate::freeze::check_no_frozen_inputs;
use crate::migration::check_migration_rules;
use crate::params::MigrationConfig;
use crate::types::{Block, Transaction, UtxoSet};
use crate::weight::check_block_cost;

/// Observable structural transaction decision used by refinement adapters.
///
/// `valid` is the deployed structural validator result. The remaining fields
/// expose the consensus-relevant subdecisions needed for audit and future
/// Coq-extracted kernel comparison.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuralTxReport {
    /// `true` iff at least two inputs spend the same outpoint.
    pub has_duplicate_inputs: bool,
    /// `true` iff every input references an output in the provided UTXO set.
    pub all_inputs_present: bool,
    /// Sum of spent values when all inputs exist; `None` otherwise.
    pub input_sum: Option<u64>,
    /// Sum of created output values.
    pub output_sum: u64,
    /// Result of the structural migration-phase rules.
    pub migration_ok: bool,
    /// Result of the frozen-input check.
    pub freeze_ok: bool,
    /// Result of `valid_tx_structural`.
    pub valid: bool,
}

/// Observable structural block decision used by refinement adapters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuralBlockReport {
    /// `true` iff every transaction applies sequentially under structural rules.
    pub transitions_ok: bool,
    /// `true` iff the block satisfies the cost bound.
    pub cost_ok: bool,
    /// Final structural UTXO set when both transition and cost checks accept.
    pub final_utxo: Option<UtxoSet>,
    /// Boolean projection of `validate_and_apply_block_structural`.
    pub valid: bool,
}

/// Structural transition-kernel contract.
///
/// The deployed implementation delegates to the existing Rust structural
/// entrypoints. A verified/extracted implementation must match this observable
/// contract extensionally: same accept/reject decisions, same final UTXO
/// snapshots, and same transaction subdecision reports.
pub trait TransitionKernel {
    /// Return the structural transaction report.
    fn structural_tx_report(
        &self,
        utxo_set: &UtxoSet,
        tx: &Transaction,
        height: u64,
        config: &MigrationConfig,
    ) -> StructuralTxReport;

    /// Return the structural block report.
    fn structural_block_report(
        &self,
        utxo_set: &UtxoSet,
        block: &Block,
        height: u64,
        config: &MigrationConfig,
    ) -> StructuralBlockReport;

    /// Boolean structural transaction validator.
    fn valid_tx_structural(
        &self,
        utxo_set: &UtxoSet,
        tx: &Transaction,
        height: u64,
        config: &MigrationConfig,
    ) -> bool;

    /// Pure-copy `delta_tx`: apply the transaction to a cloned UTXO set.
    fn delta_tx(&self, utxo_set: &UtxoSet, tx: &Transaction) -> UtxoSet;

    /// Sequential structural block transition without block-cost validation.
    fn apply_block_transitions_structural(
        &self,
        utxo_set: &UtxoSet,
        block: &Block,
        height: u64,
        config: &MigrationConfig,
    ) -> Option<UtxoSet>;

    /// Sequential structural block transition plus block-cost validation.
    fn validate_and_apply_block_structural(
        &self,
        utxo_set: &UtxoSet,
        block: &Block,
        height: u64,
        config: &MigrationConfig,
    ) -> Option<UtxoSet>;

    /// Boolean projection of `validate_and_apply_block_structural`.
    fn valid_block_structural(
        &self,
        utxo_set: &UtxoSet,
        block: &Block,
        height: u64,
        config: &MigrationConfig,
    ) -> bool;
}

/// Deployed Rust structural transition adapter.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DeployedTransitionKernel;

impl DeployedTransitionKernel {
    /// Construct the deployed structural transition adapter.
    pub const fn new() -> Self {
        Self
    }
}

impl TransitionKernel for DeployedTransitionKernel {
    fn structural_tx_report(
        &self,
        utxo_set: &UtxoSet,
        tx: &Transaction,
        height: u64,
        config: &MigrationConfig,
    ) -> StructuralTxReport {
        let has_duplicate_inputs = has_duplicate_inputs(tx);
        let all_inputs_present = tx
            .inputs
            .iter()
            .all(|input| utxo_set.get(&input.outpoint).is_some());
        let input_sum = input_value_sum(utxo_set, tx);
        let output_sum = tx.outputs.iter().map(|output| output.value).sum();
        let migration_ok = check_migration_rules(height, tx, utxo_set, config);
        let freeze_ok = check_no_frozen_inputs(height, tx, utxo_set, config);
        let valid = crate::valid_tx_structural(utxo_set, tx, height, config);

        StructuralTxReport {
            has_duplicate_inputs,
            all_inputs_present,
            input_sum,
            output_sum,
            migration_ok,
            freeze_ok,
            valid,
        }
    }

    fn structural_block_report(
        &self,
        utxo_set: &UtxoSet,
        block: &Block,
        height: u64,
        config: &MigrationConfig,
    ) -> StructuralBlockReport {
        let transition_final_utxo =
            crate::apply_block_transitions_structural(utxo_set, block, height, config);
        let transitions_ok = transition_final_utxo.is_some();
        let cost_ok = check_block_cost(block);
        let final_utxo = if cost_ok { transition_final_utxo } else { None };
        let valid = final_utxo.is_some();

        StructuralBlockReport {
            transitions_ok,
            cost_ok,
            final_utxo,
            valid,
        }
    }

    fn valid_tx_structural(
        &self,
        utxo_set: &UtxoSet,
        tx: &Transaction,
        height: u64,
        config: &MigrationConfig,
    ) -> bool {
        crate::valid_tx_structural(utxo_set, tx, height, config)
    }

    fn delta_tx(&self, utxo_set: &UtxoSet, tx: &Transaction) -> UtxoSet {
        let mut next_utxo = utxo_set.clone();
        crate::delta_tx(&mut next_utxo, tx);
        next_utxo
    }

    fn apply_block_transitions_structural(
        &self,
        utxo_set: &UtxoSet,
        block: &Block,
        height: u64,
        config: &MigrationConfig,
    ) -> Option<UtxoSet> {
        crate::apply_block_transitions_structural(utxo_set, block, height, config)
    }

    fn validate_and_apply_block_structural(
        &self,
        utxo_set: &UtxoSet,
        block: &Block,
        height: u64,
        config: &MigrationConfig,
    ) -> Option<UtxoSet> {
        crate::validate_and_apply_block_structural(utxo_set, block, height, config)
    }

    fn valid_block_structural(
        &self,
        utxo_set: &UtxoSet,
        block: &Block,
        height: u64,
        config: &MigrationConfig,
    ) -> bool {
        crate::valid_block_structural(utxo_set, block, height, config)
    }
}

fn has_duplicate_inputs(tx: &Transaction) -> bool {
    for i in 0..tx.inputs.len() {
        for j in (i + 1)..tx.inputs.len() {
            if tx.inputs[i].outpoint == tx.inputs[j].outpoint {
                return true;
            }
        }
    }
    false
}

fn input_value_sum(utxo_set: &UtxoSet, tx: &Transaction) -> Option<u64> {
    tx.inputs.iter().try_fold(0u64, |sum, input| {
        utxo_set
            .get(&input.outpoint)
            .map(|output| sum + output.value)
    })
}

#[cfg(test)]
mod tests {
    use super::{DeployedTransitionKernel, TransitionKernel};
    use crate::params::MigrationConfig;
    use crate::types::{Block, OutPoint, Output, Transaction, TxInput, TxOutput, UtxoSet};
    use crate::{compute_txid, valid_tx, valid_tx_structural, validate_and_apply_block_structural};

    fn config() -> MigrationConfig {
        MigrationConfig {
            announcement_height: 100,
            cutover_height: 160,
        }
    }

    fn outpoint(id: u8) -> OutPoint {
        let mut txid = [0u8; 32];
        txid[0] = id;
        txid[31] = id.wrapping_mul(17);
        OutPoint { txid, vout: 0 }
    }

    fn utxo_output(script_version: u8, value: u64) -> Output {
        Output {
            script_version,
            commitment: [script_version; 32],
            value,
        }
    }

    fn tx_output(script_version: u8, value: u64) -> TxOutput {
        TxOutput {
            script_version,
            commitment: [script_version.wrapping_add(1); 32],
            value,
        }
    }

    fn tx_input(outpoint: OutPoint) -> TxInput {
        TxInput {
            outpoint,
            witness: vec![0xDE, 0xAD],
        }
    }

    fn singleton_utxo(outpoint: OutPoint, output: Output) -> UtxoSet {
        let mut utxo = UtxoSet::new();
        utxo.insert(outpoint, output);
        utxo
    }

    fn tx(inputs: Vec<TxInput>, outputs: Vec<TxOutput>) -> Transaction {
        Transaction {
            version: 2,
            inputs,
            outputs,
            locktime: 0,
        }
    }

    #[test]
    fn transaction_report_exposes_rejection_subdecisions() {
        let kernel = DeployedTransitionKernel::new();
        let config = config();

        let missing = tx(vec![tx_input(outpoint(1))], vec![tx_output(2, 1)]);
        let missing_report = kernel.structural_tx_report(&UtxoSet::new(), &missing, 50, &config);
        assert!(!missing_report.has_duplicate_inputs);
        assert!(!missing_report.all_inputs_present);
        assert_eq!(missing_report.input_sum, None);
        assert_eq!(missing_report.output_sum, 1);
        assert!(!missing_report.valid);

        let duplicate_outpoint = outpoint(2);
        let duplicate_utxo = singleton_utxo(duplicate_outpoint.clone(), utxo_output(0, 2));
        let duplicate = tx(
            vec![
                tx_input(duplicate_outpoint.clone()),
                tx_input(duplicate_outpoint),
            ],
            vec![tx_output(2, 1)],
        );
        let duplicate_report =
            kernel.structural_tx_report(&duplicate_utxo, &duplicate, 50, &config);
        assert!(duplicate_report.has_duplicate_inputs);
        assert!(duplicate_report.all_inputs_present);
        assert_eq!(duplicate_report.input_sum, Some(4));
        assert!(!duplicate_report.valid);

        let inflated_outpoint = outpoint(3);
        let inflated_utxo = singleton_utxo(inflated_outpoint.clone(), utxo_output(0, 1));
        let inflated = tx(vec![tx_input(inflated_outpoint)], vec![tx_output(2, 2)]);
        let inflated_report = kernel.structural_tx_report(&inflated_utxo, &inflated, 50, &config);
        assert_eq!(inflated_report.input_sum, Some(1));
        assert_eq!(inflated_report.output_sum, 2);
        assert!(!inflated_report.valid);
    }

    #[test]
    fn transaction_report_exposes_migration_and_freeze_boundaries() {
        let kernel = DeployedTransitionKernel::new();
        let config = config();

        let legacy_after_ha_outpoint = outpoint(4);
        let legacy_after_ha_utxo =
            singleton_utxo(legacy_after_ha_outpoint.clone(), utxo_output(0, 1));
        let legacy_after_ha = tx(
            vec![tx_input(legacy_after_ha_outpoint)],
            vec![tx_output(0, 1)],
        );
        let legacy_after_ha_report =
            kernel.structural_tx_report(&legacy_after_ha_utxo, &legacy_after_ha, 100, &config);
        assert!(!legacy_after_ha_report.migration_ok);
        assert!(!legacy_after_ha_report.valid);

        let frozen_outpoint = outpoint(5);
        let frozen_utxo = singleton_utxo(frozen_outpoint.clone(), utxo_output(0, 1));
        let frozen = tx(vec![tx_input(frozen_outpoint)], vec![tx_output(2, 1)]);
        let frozen_report = kernel.structural_tx_report(&frozen_utxo, &frozen, 160, &config);
        assert!(!frozen_report.freeze_ok);
        assert!(!frozen_report.valid);
    }

    #[test]
    fn deployed_kernel_preserves_structural_pq_boundary() {
        let kernel = DeployedTransitionKernel::new();
        let config = config();
        let outpoint = outpoint(6);
        let utxo = singleton_utxo(outpoint.clone(), utxo_output(2, 1));
        let tx = tx(vec![tx_input(outpoint)], vec![tx_output(2, 1)]);

        let report = kernel.structural_tx_report(&utxo, &tx, 50, &config);

        assert!(report.valid);
        assert!(kernel.valid_tx_structural(&utxo, &tx, 50, &config));
        assert!(valid_tx_structural(&utxo, &tx, 50, &config));
        assert!(!valid_tx(&utxo, &tx, 50, &config));
    }

    #[test]
    fn deployed_kernel_block_report_matches_structural_api() {
        let kernel = DeployedTransitionKernel::new();
        let config = config();
        let root = outpoint(7);
        let utxo = singleton_utxo(root.clone(), utxo_output(0, 2));
        let tx1 = tx(vec![tx_input(root.clone())], vec![tx_output(0, 2)]);
        let tx1_out = OutPoint {
            txid: compute_txid(&tx1),
            vout: 0,
        };
        let tx2 = tx(vec![tx_input(tx1_out.clone())], vec![tx_output(2, 1)]);
        let tx2_out = OutPoint {
            txid: compute_txid(&tx2),
            vout: 0,
        };
        let block: Block = vec![tx1, tx2];

        let report = kernel.structural_block_report(&utxo, &block, 50, &config);
        let api_result = validate_and_apply_block_structural(&utxo, &block, 50, &config);

        assert!(report.transitions_ok);
        assert!(report.cost_ok);
        assert!(report.valid);
        assert_eq!(report.final_utxo, api_result);

        let final_utxo = report.final_utxo.expect("structural block should apply");
        assert!(!final_utxo.contains_key(&root));
        assert!(!final_utxo.contains_key(&tx1_out));
        assert!(final_utxo.contains_key(&tx2_out));
        assert!(utxo.contains_key(&root));
    }

    #[test]
    fn deployed_kernel_delta_tx_is_pure_copy_adapter() {
        let kernel = DeployedTransitionKernel::new();
        let root = outpoint(8);
        let utxo = singleton_utxo(root.clone(), utxo_output(0, 2));
        let tx = tx(vec![tx_input(root.clone())], vec![tx_output(2, 1)]);
        let created = OutPoint {
            txid: compute_txid(&tx),
            vout: 0,
        };

        let next_utxo = kernel.delta_tx(&utxo, &tx);

        assert!(utxo.contains_key(&root));
        assert!(!next_utxo.contains_key(&root));
        assert!(next_utxo.contains_key(&created));
    }
}
