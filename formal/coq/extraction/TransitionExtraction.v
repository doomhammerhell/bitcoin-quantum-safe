(* TransitionExtraction: extraction-facing wrappers for PO-5 transition refinement.
 *
 * This module exposes deterministic UTXO transition and structural validation
 * functions from UTXOTransitions.v. The extraction boundary compares the Coq
 * association-list model against a canonical Rust HashMap projection; it does
 * not claim SHA-256 txid, HashMap, compiler, or cryptographic witness
 * verification correctness.
 *)

From Coq Require Import Extraction.
From BitcoinPQ Require Import UTXOTransitions.

(* Native extraction profile shared with the other refinement harnesses. *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive prod => "( * )" [ "(,)" ].
Extract Inductive nat => int [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inlined Constant Nat.add => "( + )".
Extract Inlined Constant Nat.mul => "( * )".
Extract Inlined Constant Init.Nat.add => "( + )".
Extract Inlined Constant Init.Nat.mul => "( * )".
Extract Constant Nat.add => "( + )".
Extract Constant Nat.mul => "( * )".
Extract Inlined Constant Nat.leb => "( <= )".
Extract Inlined Constant Nat.ltb => "( < )".
Extract Inlined Constant Nat.eqb => "( = )".
Extract Constant Nat.leb => "( <= )".
Extract Constant Nat.ltb => "( < )".
Extract Constant Nat.eqb => "( = )".
Extract Constant C_MAX => "4000000".
Extract Constant cost_input => "(fun witness_len -> witness_len + 144)".
Extract Constant base_weight => "(fun num_outputs -> 40 + (num_outputs * 164))".
Extract Constant weight_tx =>
  "(fun num_inputs witness_lens num_outputs -> ((10 + (num_inputs * 36) + (num_outputs * 41)) * 4) + List.fold_left ( + ) 0 witness_lens)".

Module TransitionExtraction.

Definition extract_lookup := lookup.
Definition extract_remove := remove.
Definition extract_remove_inputs := remove_inputs.
Definition extract_add_outputs := add_outputs.
Definition extract_delta_tx := delta_tx.

Definition extract_has_duplicate_inputs := has_duplicate_inputs.
Definition extract_sum_input_values := sum_input_values.
Definition extract_sum_output_values := sum_output_values.
Definition extract_check_migration_rules_structural := check_migration_rules_structural.
Definition extract_check_no_frozen_inputs_structural := check_no_frozen_inputs_structural.
Definition extract_valid_tx_structural := valid_tx_structural.

Definition extract_cost_input := cost_input.
Definition extract_base_weight := base_weight.
Definition extract_cost_tx := cost_tx.
Definition extract_weight_tx := weight_tx.
Definition extract_block_cost := block_cost.
Definition extract_check_block_cost_bool := check_block_cost_bool.
Definition extract_cost_tx_structural := cost_tx_structural.
Definition extract_block_cost_structural := block_cost_structural.
Definition extract_check_block_cost_structural := check_block_cost_structural.
Definition extract_valid_block_transitions_structural := valid_block_transitions_structural.
Definition extract_valid_block_structural := valid_block_structural.

End TransitionExtraction.
