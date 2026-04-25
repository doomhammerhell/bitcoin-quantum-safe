//! Weight_Accountant: cost function and block cost invariant.
//!
//! Computes per-transaction cost (Cost(tx) ≤ α · weight(tx)) and enforces
//! the block cost invariant (Σ Cost(tx) ≤ C_max = 4,000,000 WU).
//! PQ witness data is accounted at 1 WU/byte under the SegWit witness discount.

use crate::params::{ALPHA, C_MAX};
use crate::types::{Block, Transaction};

// ---------------------------------------------------------------------------
// Constants for weight calculation
// ---------------------------------------------------------------------------

/// Non-witness weight multiplier: non-witness data is counted at 4 WU/byte.
const NON_WITNESS_SCALE: u64 = 4;

/// Input overhead in weight units.
///
/// Each input has a fixed non-witness component:
///   outpoint = txid (32 bytes) + vout (4 bytes) = 36 bytes
///   At 4 WU/byte → 144 WU per input.
const INPUT_OVERHEAD_WU: u64 = 144;

/// Base transaction overhead in weight units.
///
/// Fixed non-witness fields:
///   version (4 bytes) + locktime (4 bytes) + input count varint (~1 byte)
///   + output count varint (~1 byte) = ~10 bytes
///     At 4 WU/byte → 40 WU.
const BASE_TX_OVERHEAD_WU: u64 = 40;

/// Per-output weight in weight units.
///
/// Each output has:
///   script_version (1 byte) + commitment (32 bytes) + value (8 bytes) = 41 bytes
///   At 4 WU/byte → 164 WU per output.
const OUTPUT_WU: u64 = 164;

// ---------------------------------------------------------------------------
// Cost functions
// ---------------------------------------------------------------------------

/// Compute the cost of a single input in weight units.
///
/// `cost_input(witness) = witness.len() * 1 WU/byte + INPUT_OVERHEAD_WU`
///
/// The witness bytes are accounted at 1 WU/byte under the SegWit witness
/// discount. The overhead covers the non-witness input structure (outpoint)
/// at 4 WU/byte.
pub fn cost_input(witness: &[u8]) -> u64 {
    witness.len() as u64 + INPUT_OVERHEAD_WU
}

/// Compute the base weight of a transaction (non-witness data) in weight units.
///
/// `base_weight(tx) = BASE_TX_OVERHEAD_WU + outputs.len() * OUTPUT_WU`
///
/// This covers version, locktime, varint counts, and all output data,
/// all scaled at 4 WU/byte.
pub fn base_weight(tx: &Transaction) -> u64 {
    BASE_TX_OVERHEAD_WU + (tx.outputs.len() as u64) * OUTPUT_WU
}

/// Compute the total cost of a transaction in weight units.
///
/// `Cost(tx) = Σ_i cost_input(tx.inputs[i].witness) + base_weight(tx)`
///
/// This cost function satisfies `Cost(tx) ≤ α · weight(tx)` for α = 1,
/// because PQ witness bytes are already accounted at 1 WU/byte under the
/// SegWit witness discount (Req 3.1).
pub fn cost_tx(tx: &Transaction) -> u64 {
    let input_cost: u64 = tx
        .inputs
        .iter()
        .map(|input| cost_input(&input.witness))
        .sum();
    input_cost + base_weight(tx)
}

/// Compute the standard SegWit weight of a transaction.
///
/// `weight(tx) = non_witness_bytes * 4 + witness_bytes * 1`
///
/// Non-witness data includes: version, locktime, varint counts, outpoints
/// (per input), and all output data. Witness data is each input's witness
/// bytes at 1 WU/byte.
///
/// Used to verify the cost bound property: `cost_tx(tx) ≤ ALPHA * weight_tx(tx)`.
pub fn weight_tx(tx: &Transaction) -> u64 {
    // Non-witness bytes (at 4 WU/byte):
    //   version (4) + locktime (4) + input_count varint (~1) + output_count varint (~1) = ~10 bytes
    //   + per input: outpoint (36 bytes)
    //   + per output: script_version (1) + commitment (32) + value (8) = 41 bytes
    let non_witness_bytes: u64 = 10
        + (tx.inputs.len() as u64) * 36
        + (tx.outputs.len() as u64) * 41;

    // Witness bytes (at 1 WU/byte):
    let witness_bytes: u64 = tx
        .inputs
        .iter()
        .map(|input| input.witness.len() as u64)
        .sum();

    non_witness_bytes * NON_WITNESS_SCALE + witness_bytes
}

/// Check the block cost invariant: `Σ Cost(tx) ≤ C_max`.
///
/// Returns `true` if the total cost of all transactions in the block
/// does not exceed `C_MAX` (4,000,000 WU). This enforces Definition 12
/// from the paper (Req 3.2, 8.1).
pub fn check_block_cost(block: &Block) -> bool {
    let total: u64 = block.iter().map(cost_tx).sum();
    total <= C_MAX
}

// ---------------------------------------------------------------------------
// Cost bound verification (for testing)
// ---------------------------------------------------------------------------

/// Verify the cost bound property: `cost_tx(tx) ≤ ALPHA * weight_tx(tx)`.
///
/// Returns `true` if the cost function is bounded by the weight function
/// scaled by α. Since α = 1, this checks `cost_tx(tx) ≤ weight_tx(tx)`.
pub fn verify_cost_bound(tx: &Transaction) -> bool {
    cost_tx(tx) <= ALPHA * weight_tx(tx)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{OutPoint, TxInput, TxOutput, Transaction};

    /// Helper: create a transaction with the given witness sizes and output count.
    fn make_tx(witness_sizes: &[usize], num_outputs: usize) -> Transaction {
        let inputs: Vec<TxInput> = witness_sizes
            .iter()
            .enumerate()
            .map(|(i, &size)| TxInput {
                outpoint: OutPoint {
                    txid: [i as u8; 32],
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

    // -- cost_input tests --

    #[test]
    fn cost_input_empty_witness() {
        assert_eq!(cost_input(&[]), INPUT_OVERHEAD_WU);
    }

    #[test]
    fn cost_input_single_byte_witness() {
        assert_eq!(cost_input(&[0x42]), 1 + INPUT_OVERHEAD_WU);
    }

    #[test]
    fn cost_input_ml_dsa_44_witness() {
        // ML-DSA-44 witness: ~3,734 bytes
        let witness = vec![0u8; 3_734];
        assert_eq!(cost_input(&witness), 3_734 + INPUT_OVERHEAD_WU);
    }

    #[test]
    fn cost_input_slh_dsa_128s_witness() {
        // SLH-DSA-128s witness: ~7,890 bytes
        let witness = vec![0u8; 7_890];
        assert_eq!(cost_input(&witness), 7_890 + INPUT_OVERHEAD_WU);
    }

    // -- base_weight tests --

    #[test]
    fn base_weight_no_outputs() {
        let tx = make_tx(&[100], 0);
        assert_eq!(base_weight(&tx), BASE_TX_OVERHEAD_WU);
    }

    #[test]
    fn base_weight_one_output() {
        let tx = make_tx(&[100], 1);
        assert_eq!(base_weight(&tx), BASE_TX_OVERHEAD_WU + OUTPUT_WU);
    }

    #[test]
    fn base_weight_multiple_outputs() {
        let tx = make_tx(&[100], 3);
        assert_eq!(base_weight(&tx), BASE_TX_OVERHEAD_WU + 3 * OUTPUT_WU);
    }

    // -- cost_tx tests --

    #[test]
    fn cost_tx_single_input_single_output() {
        let tx = make_tx(&[3_734], 1);
        let expected = (3_734 + INPUT_OVERHEAD_WU) + BASE_TX_OVERHEAD_WU + OUTPUT_WU;
        assert_eq!(cost_tx(&tx), expected);
    }

    #[test]
    fn cost_tx_multiple_inputs() {
        let tx = make_tx(&[3_734, 7_890], 1);
        let expected = (3_734 + INPUT_OVERHEAD_WU)
            + (7_890 + INPUT_OVERHEAD_WU)
            + BASE_TX_OVERHEAD_WU
            + OUTPUT_WU;
        assert_eq!(cost_tx(&tx), expected);
    }

    #[test]
    fn cost_tx_no_inputs() {
        let tx = make_tx(&[], 1);
        let expected = BASE_TX_OVERHEAD_WU + OUTPUT_WU;
        assert_eq!(cost_tx(&tx), expected);
    }

    // -- weight_tx tests --

    #[test]
    fn weight_tx_single_input_single_output() {
        let tx = make_tx(&[3_734], 1);
        // non-witness: 10 + 1*36 + 1*41 = 87 bytes → 87 * 4 = 348 WU
        // witness: 3_734 bytes → 3_734 WU
        let expected = 87 * 4 + 3_734;
        assert_eq!(weight_tx(&tx), expected);
    }

    #[test]
    fn weight_tx_no_inputs_no_outputs() {
        let tx = make_tx(&[], 0);
        // non-witness: 10 bytes → 40 WU
        // witness: 0 WU
        assert_eq!(weight_tx(&tx), 40);
    }

    // -- cost bound property --

    #[test]
    fn cost_bound_holds_ml_dsa_44() {
        let tx = make_tx(&[3_734], 1);
        assert!(verify_cost_bound(&tx));
    }

    #[test]
    fn cost_bound_holds_slh_dsa_128s() {
        let tx = make_tx(&[7_890], 1);
        assert!(verify_cost_bound(&tx));
    }

    #[test]
    fn cost_bound_holds_multisig() {
        // 2-of-3 ML-DSA-44 multisig: ~8,786 bytes witness
        let tx = make_tx(&[8_786], 1);
        assert!(verify_cost_bound(&tx));
    }

    #[test]
    fn cost_bound_holds_multiple_inputs() {
        let tx = make_tx(&[3_734, 7_890, 8_786], 2);
        assert!(verify_cost_bound(&tx));
    }

    #[test]
    fn cost_bound_holds_empty_witness() {
        let tx = make_tx(&[0], 1);
        assert!(verify_cost_bound(&tx));
    }

    // -- check_block_cost tests --

    #[test]
    fn check_block_cost_empty_block() {
        let block: Block = vec![];
        assert!(check_block_cost(&block));
    }

    #[test]
    fn check_block_cost_single_tx_within_budget() {
        let tx = make_tx(&[3_734], 1);
        let block = vec![tx];
        assert!(check_block_cost(&block));
    }

    #[test]
    fn check_block_cost_at_limit() {
        // Create a transaction with known cost, then fill a block to exactly C_MAX.
        let tx = make_tx(&[3_734], 1);
        let tx_cost = cost_tx(&tx);
        let count = (C_MAX / tx_cost) as usize;
        let block: Block = vec![tx; count];
        let total: u64 = block.iter().map(|t| cost_tx(t)).sum();
        assert!(total <= C_MAX);
        assert!(check_block_cost(&block));
    }

    #[test]
    fn check_block_cost_exceeds_limit() {
        // Fill a block well beyond C_MAX.
        let tx = make_tx(&[3_734], 1);
        let tx_cost = cost_tx(&tx);
        let count = (C_MAX / tx_cost) as usize + 100;
        let block: Block = vec![tx; count];
        assert!(!check_block_cost(&block));
    }

    // -- ML-DSA-44 single-input weight contribution --

    #[test]
    fn ml_dsa_44_witness_weight_contribution() {
        // ML-DSA-44 witness: ~3,734 bytes → 3,734 WU at 1 WU/byte
        let witness = vec![0u8; 3_734];
        // cost_input = witness_len + overhead = 3734 + 144 = 3878
        assert_eq!(cost_input(&witness), 3_878);
    }

    #[test]
    fn slh_dsa_128s_witness_weight_contribution() {
        // SLH-DSA-128s witness: ~7,890 bytes → 7,890 WU at 1 WU/byte
        let witness = vec![0u8; 7_890];
        assert_eq!(cost_input(&witness), 7_890 + 144);
    }

    #[test]
    fn multisig_2_of_3_ml_dsa_44_witness_weight_contribution() {
        // 2-of-3 ML-DSA-44 multisig: ~8,786 bytes
        let witness = vec![0u8; 8_786];
        assert_eq!(cost_input(&witness), 8_786 + 144);
    }

    #[test]
    fn one_wu_per_byte_for_pq_witness() {
        // Verify that witness bytes contribute exactly 1 WU per byte.
        for size in [1, 100, 1_000, 5_000, 16_000] {
            let witness = vec![0u8; size];
            let cost = cost_input(&witness);
            // Witness contribution = size, overhead = INPUT_OVERHEAD_WU
            assert_eq!(cost, size as u64 + INPUT_OVERHEAD_WU);
        }
    }
}
