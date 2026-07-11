//! Source-level bounded verification harnesses for consensus-critical Rust code.
//!
//! These Kani harnesses verify deployed Rust source on bounded symbolic state
//! spaces. The witness harnesses complement the unbounded Coq theorems in
//! `formal/coq/VarintConcrete.v`. The transition harnesses complement the
//! Coq-extracted PO-5 refinement matrix by checking bounded source-level
//! `valid_tx_structural`, `delta_tx`, `valid_block_structural`, and structural
//! block-application behavior before reaching cryptographic PQ witness
//! validation.

use crate::encoding::{
    is_canonical_consensus_witness, is_canonical_witness, parse_consensus_witness,
    parse_consensus_witness_layout, parse_witness, parse_witness_layout, parse_witness_trace,
    WitnessLayout,
};
use crate::params::{MigrationConfig, MAX_WITNESS_SIZE};
use crate::types::{OutPoint, Output, Transaction, TxInput, TxOutput, UtxoSet};
use crate::{
    apply_block_transitions_structural, compute_txid, delta_tx, delta_tx_insert_created_outputs,
    delta_tx_remove_spent_outputs, valid_block_structural, valid_tx_structural,
    validate_and_apply_block_structural,
};

const SOURCE_PROOF_MAX_WITNESS_LEN: usize = 5;

fn symbolic_witness<const N: usize>() -> ([u8; N], usize) {
    let bytes: [u8; N] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= N);
    (bytes, len)
}

fn assert_layout_bounds(witness: &[u8], layout: WitnessLayout) {
    assert!(layout.pk_len > 0);
    assert!(layout.sig_len > 0);
    assert!(layout.pk_start <= witness.len());
    assert!(layout.sig_start <= witness.len());

    let pk_end = layout.pk_start + layout.pk_len;
    let sig_end = layout.sig_start + layout.sig_len;
    assert!(pk_end <= witness.len());
    assert_eq!(sig_end, witness.len());
    assert!(pk_end <= layout.sig_start);
}

fn assert_materialized_matches_layout(
    witness: &[u8],
    layout: WitnessLayout,
    pk: &[u8],
    sig: &[u8],
) {
    assert_layout_bounds(witness, layout);
    assert_eq!(pk.len(), layout.pk_len);
    assert_eq!(sig.len(), layout.sig_len);

    for i in 0..SOURCE_PROOF_MAX_WITNESS_LEN {
        if i < layout.pk_len {
            assert_eq!(pk[i], witness[layout.pk_start + i]);
        }
        if i < layout.sig_len {
            assert_eq!(sig[i], witness[layout.sig_start + i]);
        }
    }
}

#[kani::proof]
#[kani::unwind(16)]
fn parse_witness_source_bounded_matches_layout() {
    let (bytes, len) = symbolic_witness::<SOURCE_PROOF_MAX_WITNESS_LEN>();
    let witness = &bytes[..len];

    match (parse_witness_layout(witness), parse_witness(witness)) {
        (Some(layout), Some((pk, sig))) => {
            assert_materialized_matches_layout(witness, layout, &pk, &sig);
        }
        (None, None) => {}
        _ => unreachable!(),
    }
}

#[kani::proof]
#[kani::unwind(16)]
fn parse_consensus_witness_source_bounded_matches_layout_below_cap() {
    let (bytes, len) = symbolic_witness::<SOURCE_PROOF_MAX_WITNESS_LEN>();
    let witness = &bytes[..len];

    assert_eq!(
        parse_consensus_witness_layout(witness),
        parse_witness_layout(witness)
    );

    match (
        parse_consensus_witness_layout(witness),
        parse_consensus_witness(witness),
    ) {
        (Some(layout), Some((pk, sig))) => {
            assert_materialized_matches_layout(witness, layout, &pk, &sig);
        }
        (None, None) => {}
        _ => unreachable!(),
    }
}

#[kani::proof]
#[kani::unwind(16)]
fn parse_witness_trace_source_bounded_matches_parser() {
    let (bytes, len) = symbolic_witness::<SOURCE_PROOF_MAX_WITNESS_LEN>();
    let witness = &bytes[..len];

    let (trace, traced_result) = parse_witness_trace(witness);
    assert!(!trace.is_empty());

    match (parse_witness_layout(witness), traced_result) {
        (Some(layout), Some((pk, sig))) => {
            assert_materialized_matches_layout(witness, layout, &pk, &sig);
        }
        (None, None) => {}
        _ => unreachable!(),
    }
}

#[kani::proof]
#[kani::unwind(16)]
fn canonical_witness_source_bounded_matches_layout_acceptance() {
    let (bytes, len) = symbolic_witness::<SOURCE_PROOF_MAX_WITNESS_LEN>();
    let witness = &bytes[..len];

    assert_eq!(
        is_canonical_witness(witness),
        parse_witness_layout(witness).is_some()
    );
    assert_eq!(
        is_canonical_consensus_witness(witness),
        parse_consensus_witness_layout(witness).is_some()
    );
}

#[kani::proof]
#[kani::unwind(4)]
fn parse_consensus_witness_source_rejects_oversized_before_parsing() {
    let witness = [0u8; MAX_WITNESS_SIZE + 1];

    assert_eq!(parse_consensus_witness_layout(&witness), None);
    assert_eq!(parse_consensus_witness(&witness), None);
    assert!(!is_canonical_consensus_witness(&witness));
}

fn transition_config() -> MigrationConfig {
    MigrationConfig {
        announcement_height: 100,
        cutover_height: 160,
    }
}

fn transition_outpoint(id: u8) -> OutPoint {
    let mut txid = [0u8; 32];
    txid[0] = id;
    txid[31] = id.wrapping_mul(17);
    OutPoint { txid, vout: 0 }
}

fn transition_utxo_output(script_version: u8, value: u64) -> Output {
    Output {
        script_version,
        commitment: [script_version; 32],
        value,
    }
}

fn transition_tx_output(script_version: u8, value: u64) -> TxOutput {
    TxOutput {
        script_version,
        commitment: [script_version.wrapping_add(1); 32],
        value,
    }
}

fn transition_tx_input(outpoint: OutPoint) -> TxInput {
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

fn transition_tx(inputs: Vec<TxInput>, outputs: Vec<TxOutput>) -> Transaction {
    Transaction {
        version: 2,
        inputs,
        outputs,
        locktime: 0,
    }
}

fn assert_utxo_output(utxo: &UtxoSet, outpoint: &OutPoint, script_version: u8, value: u64) {
    match utxo.get(outpoint) {
        Some(output) => {
            assert_eq!(output.script_version, script_version);
            assert_eq!(output.value, value);
        }
        None => unreachable!(),
    }
}

#[kani::proof]
#[kani::unwind(64)]
fn valid_tx_structural_source_rejects_missing_inputs() {
    let missing = transition_outpoint(1);
    let tx = transition_tx(vec![transition_tx_input(missing)], vec![]);

    assert!(!valid_tx_structural(
        &UtxoSet::new(),
        &tx,
        50,
        &transition_config()
    ));
}

#[kani::proof]
#[kani::unwind(64)]
fn valid_tx_structural_source_rejects_duplicate_inputs() {
    let outpoint = transition_outpoint(2);
    let tx = transition_tx(
        vec![
            transition_tx_input(outpoint.clone()),
            transition_tx_input(outpoint),
        ],
        vec![],
    );

    assert!(!valid_tx_structural(
        &UtxoSet::new(),
        &tx,
        50,
        &transition_config()
    ));
}

#[kani::proof]
#[kani::unwind(64)]
fn valid_tx_structural_source_rejects_value_inflation() {
    let outpoint = transition_outpoint(3);
    let utxo = singleton_utxo(outpoint.clone(), transition_utxo_output(0, 1));
    let tx = transition_tx(
        vec![transition_tx_input(outpoint)],
        vec![transition_tx_output(2, 2)],
    );

    assert!(!valid_tx_structural(&utxo, &tx, 50, &transition_config()));
}

#[kani::proof]
#[kani::unwind(64)]
fn valid_tx_structural_source_rejects_legacy_outputs_after_announcement() {
    let outpoint = transition_outpoint(4);
    let utxo = singleton_utxo(outpoint.clone(), transition_utxo_output(0, 1));
    let tx = transition_tx(
        vec![transition_tx_input(outpoint)],
        vec![transition_tx_output(0, 1)],
    );

    assert!(!valid_tx_structural(&utxo, &tx, 100, &transition_config()));
}

#[kani::proof]
#[kani::unwind(64)]
fn valid_tx_structural_source_rejects_frozen_legacy_spends_at_cutover() {
    let outpoint = transition_outpoint(5);
    let utxo = singleton_utxo(outpoint.clone(), transition_utxo_output(0, 1));
    let tx = transition_tx(
        vec![transition_tx_input(outpoint)],
        vec![transition_tx_output(2, 1)],
    );

    assert!(!valid_tx_structural(&utxo, &tx, 160, &transition_config()));
}

#[kani::proof]
#[kani::unwind(64)]
fn valid_tx_structural_source_accepts_legacy_to_pq_during_grace() {
    let outpoint = transition_outpoint(6);
    let utxo = singleton_utxo(outpoint.clone(), transition_utxo_output(0, 1));
    let tx = transition_tx(
        vec![transition_tx_input(outpoint)],
        vec![transition_tx_output(2, 1)],
    );

    assert!(valid_tx_structural(&utxo, &tx, 120, &transition_config()));
}

#[kani::proof]
#[kani::unwind(64)]
fn valid_tx_structural_source_accepts_pq_spend_boundary() {
    let outpoint = transition_outpoint(17);
    let utxo = singleton_utxo(outpoint.clone(), transition_utxo_output(2, 1));
    let tx = transition_tx(
        vec![transition_tx_input(outpoint)],
        vec![transition_tx_output(2, 1)],
    );

    assert!(valid_tx_structural(&utxo, &tx, 50, &transition_config()));
}

#[kani::proof]
#[kani::unwind(96)]
fn delta_tx_source_remove_phase_removes_spent_output() {
    let spent = transition_outpoint(7);
    let mut utxo = singleton_utxo(spent.clone(), transition_utxo_output(0, 1));
    let tx = transition_tx(vec![transition_tx_input(spent.clone())], vec![]);

    delta_tx_remove_spent_outputs(&mut utxo, &tx);

    assert!(!utxo.contains_key(&spent));
}

#[kani::proof]
#[kani::unwind(96)]
fn delta_tx_source_remove_phase_preserves_unspent_output() {
    let missing = transition_outpoint(8);
    let unspent = transition_outpoint(9);
    let mut utxo = singleton_utxo(unspent.clone(), transition_utxo_output(0, 2));
    let tx = transition_tx(vec![transition_tx_input(missing)], vec![]);

    delta_tx_remove_spent_outputs(&mut utxo, &tx);

    assert_utxo_output(&utxo, &unspent, 0, 2);
}

#[kani::proof]
#[kani::unwind(96)]
fn delta_tx_source_insert_phase_adds_output_at_modeled_txid() {
    let mut utxo = UtxoSet::new();
    let tx = transition_tx(vec![], vec![transition_tx_output(2, 1)]);
    let txid = transition_outpoint(10).txid;
    let out0 = OutPoint { txid, vout: 0 };

    delta_tx_insert_created_outputs(&mut utxo, &tx, txid);

    assert_utxo_output(&utxo, &out0, 2, 1);
}

#[kani::proof]
#[kani::unwind(96)]
fn delta_tx_source_empty_transaction_preserves_utxo() {
    let outpoint = transition_outpoint(11);
    let mut utxo = singleton_utxo(outpoint.clone(), transition_utxo_output(0, 1));
    let tx = transition_tx(vec![], vec![]);

    delta_tx(&mut utxo, &tx);

    assert_utxo_output(&utxo, &outpoint, 0, 1);
}

#[kani::proof]
#[kani::unwind(128)]
fn delta_tx_source_spend_and_create_uses_modeled_txid() {
    let spent = transition_outpoint(12);
    let mut utxo = singleton_utxo(spent.clone(), transition_utxo_output(0, 2));
    let tx = transition_tx(
        vec![transition_tx_input(spent.clone())],
        vec![transition_tx_output(2, 1)],
    );
    let created = OutPoint {
        txid: compute_txid(&tx),
        vout: 0,
    };

    delta_tx(&mut utxo, &tx);

    assert!(!utxo.contains_key(&spent));
    assert_utxo_output(&utxo, &created, 2, 1);
}

#[kani::proof]
#[kani::unwind(96)]
fn valid_block_structural_source_accepts_empty_block() {
    let utxo = UtxoSet::new();
    let block = Vec::new();

    assert!(valid_block_structural(
        &utxo,
        &block,
        50,
        &transition_config()
    ));
}

#[kani::proof]
#[kani::unwind(128)]
fn valid_block_structural_source_accepts_sequential_dependency() {
    let root = transition_outpoint(13);
    let utxo = singleton_utxo(root.clone(), transition_utxo_output(0, 2));
    let tx1 = transition_tx(
        vec![transition_tx_input(root)],
        vec![transition_tx_output(0, 1)],
    );
    let tx1_out = OutPoint {
        txid: compute_txid(&tx1),
        vout: 0,
    };
    let tx2 = transition_tx(
        vec![transition_tx_input(tx1_out)],
        vec![transition_tx_output(2, 1)],
    );
    let block = vec![tx1, tx2];

    assert!(valid_block_structural(
        &utxo,
        &block,
        50,
        &transition_config()
    ));
}

#[kani::proof]
#[kani::unwind(128)]
fn valid_block_structural_source_rejects_invalid_first_transaction() {
    let missing = transition_outpoint(13);
    let utxo = UtxoSet::new();
    let tx = transition_tx(
        vec![transition_tx_input(missing)],
        vec![transition_tx_output(2, 1)],
    );
    let block = vec![tx];

    assert!(!valid_block_structural(
        &utxo,
        &block,
        50,
        &transition_config()
    ));
}

#[kani::proof]
#[kani::unwind(128)]
fn valid_block_structural_source_rejects_intrablock_double_spend() {
    let spent = transition_outpoint(14);
    let utxo = singleton_utxo(spent.clone(), transition_utxo_output(0, 2));
    let tx1 = transition_tx(
        vec![transition_tx_input(spent.clone())],
        vec![transition_tx_output(2, 1)],
    );
    let tx2 = transition_tx(
        vec![transition_tx_input(spent)],
        vec![transition_tx_output(2, 1)],
    );
    let block = vec![tx1, tx2];

    assert!(!valid_block_structural(
        &utxo,
        &block,
        50,
        &transition_config()
    ));
}

#[kani::proof]
#[kani::unwind(160)]
fn apply_block_transitions_structural_source_returns_final_state_for_legacy_dependency() {
    let root = transition_outpoint(15);
    let utxo = singleton_utxo(root.clone(), transition_utxo_output(0, 2));
    let tx1 = transition_tx(
        vec![transition_tx_input(root.clone())],
        vec![transition_tx_output(0, 2)],
    );
    let tx1_out = OutPoint {
        txid: compute_txid(&tx1),
        vout: 0,
    };
    let tx2 = transition_tx(
        vec![transition_tx_input(tx1_out.clone())],
        vec![transition_tx_output(2, 1)],
    );
    let tx2_out = OutPoint {
        txid: compute_txid(&tx2),
        vout: 0,
    };
    let block = vec![tx1, tx2];

    match apply_block_transitions_structural(&utxo, &block, 50, &transition_config()) {
        Some(final_utxo) => {
            assert!(!final_utxo.contains_key(&root));
            assert!(!final_utxo.contains_key(&tx1_out));
            assert_utxo_output(&final_utxo, &tx2_out, 2, 1);
            assert_utxo_output(&utxo, &root, 0, 2);
        }
        None => unreachable!(),
    }
}

#[kani::proof]
#[kani::unwind(160)]
fn validate_and_apply_block_structural_source_matches_valid_block_projection() {
    let root = transition_outpoint(16);
    let utxo = singleton_utxo(root.clone(), transition_utxo_output(0, 1));
    let tx = transition_tx(
        vec![transition_tx_input(root)],
        vec![transition_tx_output(2, 1)],
    );
    let block = vec![tx];

    assert_eq!(
        validate_and_apply_block_structural(&utxo, &block, 50, &transition_config()).is_some(),
        valid_block_structural(&utxo, &block, 50, &transition_config())
    );
}

#[kani::proof]
#[kani::unwind(160)]
fn validate_and_apply_block_structural_source_accepts_pq_boundary() {
    let root = transition_outpoint(18);
    let utxo = singleton_utxo(root.clone(), transition_utxo_output(2, 1));
    let tx = transition_tx(
        vec![transition_tx_input(root.clone())],
        vec![transition_tx_output(2, 1)],
    );
    let created = OutPoint {
        txid: compute_txid(&tx),
        vout: 0,
    };
    let block = vec![tx];

    match validate_and_apply_block_structural(&utxo, &block, 50, &transition_config()) {
        Some(final_utxo) => {
            assert!(!final_utxo.contains_key(&root));
            assert_utxo_output(&final_utxo, &created, 2, 1);
        }
        None => unreachable!(),
    }
}
