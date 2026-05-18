//! Source-level bounded verification harnesses for the consensus witness parser.
//!
//! These Kani harnesses verify the deployed Rust source on symbolic byte arrays.
//! They complement the unbounded Coq theorems in `formal/coq/VarintConcrete.v`:
//! Coq proves the mathematical parser/canonicality properties, while Kani checks
//! that the Rust implementation maintains those properties over a bounded
//! symbolic source-level state space.

use crate::encoding::{
    is_canonical_consensus_witness, is_canonical_witness, parse_consensus_witness,
    parse_consensus_witness_layout, parse_witness, parse_witness_layout, parse_witness_trace,
    WitnessLayout,
};
use crate::params::MAX_WITNESS_SIZE;

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
