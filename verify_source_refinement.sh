#!/usr/bin/env bash
set -euo pipefail

if ! command -v cargo >/dev/null 2>&1; then
  echo "cargo is required for source-level Rust refinement verification" >&2
  exit 127
fi

if ! cargo kani --version >/dev/null 2>&1; then
  echo "cargo-kani is required. Install with: cargo install --locked kani-verifier --version 0.67.0" >&2
  exit 127
fi

if [[ -z "${KANI_HOME:-}" ]]; then
  kani_version="$(cargo kani --version | awk '{print $2}')"
  kani_release_dir="${HOME}/.kani/kani-${kani_version}"
  if [[ ! -x "${kani_release_dir}/toolchain/bin/cargo" \
    && -x "${kani_release_dir}/kani-${kani_version}/toolchain/bin/cargo" ]]; then
    export KANI_HOME="${kani_release_dir}"
  fi
fi

echo "Running Kani source-level bounded refinement harnesses (PO-8 witness parser + PO-5 transition functions)"

if (($# > 0)); then
  cargo kani --output-format terse --default-unwind 16 "$@"
  exit 0
fi

harnesses=(
  parse_witness_source_bounded_matches_layout
  parse_consensus_witness_source_bounded_matches_layout_below_cap
  parse_witness_trace_source_bounded_matches_parser
  canonical_witness_source_bounded_matches_layout_acceptance
  parse_consensus_witness_source_rejects_oversized_before_parsing
  valid_tx_source_rejects_missing_inputs
  valid_tx_source_rejects_duplicate_inputs
  valid_tx_source_rejects_value_inflation
  valid_tx_source_rejects_legacy_outputs_after_announcement
  valid_tx_source_rejects_frozen_legacy_spends_at_cutover
  valid_tx_source_accepts_legacy_to_pq_during_grace
  delta_tx_source_remove_phase_removes_spent_output
  delta_tx_source_remove_phase_preserves_unspent_output
  delta_tx_source_insert_phase_adds_output_at_modeled_txid
  delta_tx_source_empty_transaction_preserves_utxo
  delta_tx_source_spend_and_create_uses_modeled_txid
  valid_block_source_accepts_empty_block
  valid_block_source_accepts_sequential_dependency
  valid_block_source_rejects_invalid_first_transaction
  valid_block_source_rejects_intrablock_double_spend
)

for harness in "${harnesses[@]}"; do
  echo "==> ${harness}"
  cargo kani --output-format terse --default-unwind 16 --harness "${harness}"
done
