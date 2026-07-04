(* ExtractTransitionVectors: OCaml extraction driver for PO-5 transition vectors.
 *
 * The extracted functions cover the deterministic structural UTXO transition
 * boundary: lookup/remove/add, structural transaction validation, sequential
 * block validation, executable block-application final states, and cost checks.
 *)

From Coq Require Import Extraction.
From BitcoinPQ.extraction Require Import TransitionExtraction.

Extraction Language OCaml.

Extraction "transition_extracted.ml"
  TransitionExtraction.extract_lookup
  TransitionExtraction.extract_remove
  TransitionExtraction.extract_remove_inputs
  TransitionExtraction.extract_add_outputs
  TransitionExtraction.extract_delta_tx
  TransitionExtraction.extract_has_duplicate_inputs
  TransitionExtraction.extract_sum_input_values
  TransitionExtraction.extract_sum_output_values
  TransitionExtraction.extract_check_migration_rules_structural
  TransitionExtraction.extract_check_no_frozen_inputs_structural
  TransitionExtraction.extract_valid_tx_structural
  TransitionExtraction.extract_cost_input
  TransitionExtraction.extract_base_weight
  TransitionExtraction.extract_cost_tx
  TransitionExtraction.extract_weight_tx
  TransitionExtraction.extract_block_cost
  TransitionExtraction.extract_check_block_cost_bool
  TransitionExtraction.extract_cost_tx_structural
  TransitionExtraction.extract_block_cost_structural
  TransitionExtraction.extract_check_block_cost_structural
  TransitionExtraction.extract_valid_block_transitions_structural
  TransitionExtraction.extract_valid_block_structural
  TransitionExtraction.extract_apply_block_transitions_structural
  TransitionExtraction.extract_apply_valid_block_structural.
