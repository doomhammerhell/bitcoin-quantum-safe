(* transition_kernel_refinement.ml: PO-5 transition-kernel adapter oracle.
 *
 * This harness wraps the Coq-extracted structural transition functions behind
 * a CoqExtractedTransitionKernel oracle. It emits per-case JSON witnesses for
 * the observable reports exposed by the Rust TransitionKernel adapter:
 * StructuralTxReport and StructuralBlockReport. The comparison boundary is the
 * explicit nat-outpoint projection used by transition_refinement.ml.
 *)

open Transition_extracted

let option_is_some = function
  | None -> false
  | Some _ -> true

let output script_version value =
  { script_version; value }

let tx_output tx_script_version tx_value =
  { tx_script_version; tx_value }

let tx inputs outputs =
  { inputs; outputs }

let config =
  { announcement_height = 100; cutover_height = 160 }

module CoqExtractedTransitionKernel = struct
  type structural_tx_report = {
    tx_report_has_duplicate_inputs : bool;
    tx_report_all_inputs_present : bool;
    tx_report_input_sum : int option;
    tx_report_output_sum : int;
    tx_report_migration_ok : bool;
    tx_report_freeze_ok : bool;
    tx_report_valid : bool;
  }

  type structural_block_report = {
    block_report_transitions_ok : bool;
    block_report_cost_ok : bool;
    block_report_final_utxo : utxoSet option;
    block_report_valid : bool;
  }

  let structural_tx_report utxo body height migration_config =
    let input_sum = TransitionExtraction.extract_sum_input_values utxo body.inputs in
    {
      tx_report_has_duplicate_inputs =
        TransitionExtraction.extract_has_duplicate_inputs body;
      tx_report_all_inputs_present = option_is_some input_sum;
      tx_report_input_sum = input_sum;
      tx_report_output_sum =
        TransitionExtraction.extract_sum_output_values body.outputs;
      tx_report_migration_ok =
        TransitionExtraction.extract_check_migration_rules_structural
          height body utxo migration_config;
      tx_report_freeze_ok =
        TransitionExtraction.extract_check_no_frozen_inputs_structural
          height body utxo migration_config;
      tx_report_valid =
        TransitionExtraction.extract_valid_tx_structural
          utxo body height migration_config;
    }

  let structural_block_report utxo block height migration_config fresh_id =
    let transition_final_utxo =
      TransitionExtraction.extract_apply_block_transitions_structural
        utxo block height migration_config fresh_id
    in
    let cost_ok = TransitionExtraction.extract_check_block_cost_structural block in
    let final_utxo = if cost_ok then transition_final_utxo else None in
    {
      block_report_transitions_ok = option_is_some transition_final_utxo;
      block_report_cost_ok = cost_ok;
      block_report_final_utxo = final_utxo;
      block_report_valid = option_is_some final_utxo;
    }
end

type tx_case = {
  tx_name : string;
  tx_height : int;
  tx_utxo : utxoSet;
  tx_body : transaction;
  tx_fresh_id : int;
  tx_observed_ids : int list;
}

let tx_cases =
  [
    {
      tx_name = "empty-transaction";
      tx_height = 50;
      tx_utxo = [];
      tx_body = tx [] [];
      tx_fresh_id = 100;
      tx_observed_ids = [];
    };
    {
      tx_name = "valid-preactivation-legacy-to-legacy";
      tx_height = 99;
      tx_utxo = [ (1, output 0 50_000); (9, output 2 7_000) ];
      tx_body = tx [ 1 ] [ tx_output 0 40_000 ];
      tx_fresh_id = 100;
      tx_observed_ids = [ 1; 9; 100 ];
    };
    {
      tx_name = "valid-grace-legacy-to-pq";
      tx_height = 120;
      tx_utxo = [ (2, output 0 50_000) ];
      tx_body = tx [ 2 ] [ tx_output 2 50_000 ];
      tx_fresh_id = 110;
      tx_observed_ids = [ 2; 110 ];
    };
    {
      tx_name = "structural-pq-spend-boundary";
      tx_height = 50;
      tx_utxo = [ (13, output 2 50_000) ];
      tx_body = tx [ 13 ] [ tx_output 2 50_000 ];
      tx_fresh_id = 210;
      tx_observed_ids = [ 13; 210 ];
    };
    {
      tx_name = "missing-input";
      tx_height = 50;
      tx_utxo = [];
      tx_body = tx [ 99 ] [ tx_output 2 1 ];
      tx_fresh_id = 120;
      tx_observed_ids = [ 99; 120 ];
    };
    {
      tx_name = "duplicate-input";
      tx_height = 50;
      tx_utxo = [ (3, output 0 100) ];
      tx_body = tx [ 3; 3 ] [ tx_output 2 50 ];
      tx_fresh_id = 130;
      tx_observed_ids = [ 3; 130 ];
    };
    {
      tx_name = "value-inflation";
      tx_height = 50;
      tx_utxo = [ (4, output 0 50) ];
      tx_body = tx [ 4 ] [ tx_output 2 100 ];
      tx_fresh_id = 140;
      tx_observed_ids = [ 4; 140 ];
    };
    {
      tx_name = "legacy-output-after-ha";
      tx_height = 100;
      tx_utxo = [ (5, output 0 100) ];
      tx_body = tx [ 5 ] [ tx_output 0 100 ];
      tx_fresh_id = 150;
      tx_observed_ids = [ 5; 150 ];
    };
    {
      tx_name = "frozen-legacy-spend-at-cutover";
      tx_height = 160;
      tx_utxo = [ (6, output 0 100) ];
      tx_body = tx [ 6 ] [ tx_output 2 100 ];
      tx_fresh_id = 160;
      tx_observed_ids = [ 6; 160 ];
    };
    {
      tx_name = "post-cutover-taproot-rejection";
      tx_height = 160;
      tx_utxo = [ (7, output 1 100) ];
      tx_body = tx [ 7 ] [ tx_output 2 100 ];
      tx_fresh_id = 170;
      tx_observed_ids = [ 7; 170 ];
    };
    {
      tx_name = "mixed-inputs-post-cutover";
      tx_height = 160;
      tx_utxo = [ (8, output 2 60); (9, output 0 40) ];
      tx_body = tx [ 8; 9 ] [ tx_output 2 100 ];
      tx_fresh_id = 180;
      tx_observed_ids = [ 8; 9; 180 ];
    };
    {
      tx_name = "multi-input-fee-conservation";
      tx_height = 120;
      tx_utxo = [ (10, output 0 70); (11, output 0 50) ];
      tx_body = tx [ 10; 11 ] [ tx_output 2 100; tx_output 2 10 ];
      tx_fresh_id = 190;
      tx_observed_ids = [ 10; 11; 190; 191 ];
    };
    {
      tx_name = "script-version-255-frozen";
      tx_height = 160;
      tx_utxo = [ (12, output 255 100) ];
      tx_body = tx [ 12 ] [ tx_output 2 100 ];
      tx_fresh_id = 200;
      tx_observed_ids = [ 12; 200 ];
    };
  ]

type block_case = {
  block_name : string;
  block_height : int;
  block_utxo : utxoSet;
  block_txs : transaction list;
  block_fresh_id : int;
  block_observed_ids : int list;
}

let block_cases =
  [
    {
      block_name = "empty-block";
      block_height = 50;
      block_utxo = [];
      block_txs = [];
      block_fresh_id = 300;
      block_observed_ids = [];
    };
    {
      block_name = "single-valid-block";
      block_height = 50;
      block_utxo = [ (20, output 0 50) ];
      block_txs = [ tx [ 20 ] [ tx_output 2 50 ] ];
      block_fresh_id = 310;
      block_observed_ids = [ 20; 310 ];
    };
    {
      block_name = "structural-pq-spend-block-boundary";
      block_height = 50;
      block_utxo = [ (23, output 2 50) ];
      block_txs = [ tx [ 23 ] [ tx_output 2 50 ] ];
      block_fresh_id = 350;
      block_observed_ids = [ 23; 350 ];
    };
    {
      block_name = "invalid-missing-input-block";
      block_height = 50;
      block_utxo = [];
      block_txs = [ tx [ 299 ] [ tx_output 2 1 ] ];
      block_fresh_id = 320;
      block_observed_ids = [ 299; 320 ];
    };
    {
      block_name = "sequential-intrablock-legacy-dependency";
      block_height = 50;
      block_utxo = [ (21, output 0 100) ];
      block_txs =
        [
          tx [ 21 ] [ tx_output 0 100 ];
          tx [ 330 ] [ tx_output 2 90 ];
        ];
      block_fresh_id = 330;
      block_observed_ids = [ 21; 330; 331 ];
    };
    {
      block_name = "intrablock-double-spend-rejected";
      block_height = 50;
      block_utxo = [ (22, output 0 100) ];
      block_txs =
        [
          tx [ 22 ] [ tx_output 2 50 ];
          tx [ 22 ] [ tx_output 2 50 ];
        ];
      block_fresh_id = 340;
      block_observed_ids = [ 22; 340; 341 ];
    };
  ]

let json_string value =
  let buffer = Buffer.create (String.length value + 2) in
  Buffer.add_char buffer '"';
  String.iter
    (function
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\b' -> Buffer.add_string buffer "\\b"
      | '\012' -> Buffer.add_string buffer "\\f"
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\r' -> Buffer.add_string buffer "\\r"
      | '\t' -> Buffer.add_string buffer "\\t"
      | c -> Buffer.add_char buffer c)
    value;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let json_bool value =
  if value then "true" else "false"

let json_option_nat = function
  | None -> "null"
  | Some n -> string_of_int n

let rec json_int_list = function
  | [] -> "[]"
  | xs ->
      "["
      ^ String.concat ", " (List.map string_of_int xs)
      ^ "]"

let json_observed_output = function
  | None -> "\"output\": null"
  | Some out ->
      Printf.sprintf
        "\"output\": {\"script_version\": %d, \"value\": %d}"
        out.script_version out.value

let json_state_entry utxo id =
  let out = TransitionExtraction.extract_lookup utxo id in
  Printf.sprintf "{\"id\": %d, \"present\": %s, %s}"
    id (json_bool (option_is_some out)) (json_observed_output out)

let json_state observed_ids utxo =
  "["
  ^ String.concat ", " (List.map (json_state_entry utxo) observed_ids)
  ^ "]"

let json_tx_output out =
  Printf.sprintf "{\"script_version\": %d, \"value\": %d}"
    out.tx_script_version out.tx_value

let json_transaction body =
  Printf.sprintf "{\"inputs\": %s, \"outputs\": [%s]}"
    (json_int_list body.inputs)
    (String.concat ", " (List.map json_tx_output body.outputs))

let json_block_tx body =
  json_transaction body

let json_block txs =
  "[" ^ String.concat ", " (List.map json_block_tx txs) ^ "]"

let json_tx_report report =
  let open CoqExtractedTransitionKernel in
  Printf.sprintf
    "{\
     \"has_duplicate_inputs\": %s, \
     \"all_inputs_present\": %s, \
     \"input_sum\": %s, \
     \"output_sum\": %d, \
     \"migration_ok\": %s, \
     \"freeze_ok\": %s, \
     \"valid\": %s\
     }"
    (json_bool report.tx_report_has_duplicate_inputs)
    (json_bool report.tx_report_all_inputs_present)
    (json_option_nat report.tx_report_input_sum)
    report.tx_report_output_sum
    (json_bool report.tx_report_migration_ok)
    (json_bool report.tx_report_freeze_ok)
    (json_bool report.tx_report_valid)

let json_final_state observed_ids = function
  | None -> "null"
  | Some utxo -> json_state observed_ids utxo

let json_block_report observed_ids report =
  let open CoqExtractedTransitionKernel in
  Printf.sprintf
    "{\
     \"transitions_ok\": %s, \
     \"cost_ok\": %s, \
     \"valid\": %s, \
     \"final_utxo\": %s\
     }"
    (json_bool report.block_report_transitions_ok)
    (json_bool report.block_report_cost_ok)
    (json_bool report.block_report_valid)
    (json_final_state observed_ids report.block_report_final_utxo)

let json_tx_case case_index case =
  let report =
    CoqExtractedTransitionKernel.structural_tx_report
      case.tx_utxo case.tx_body case.tx_height config
  in
  Printf.sprintf
    "{\
     \"kind\": \"transaction\", \
     \"index\": %d, \
     \"name\": %s, \
     \"height\": %d, \
     \"fresh_id\": %d, \
     \"observed_ids\": %s, \
     \"pre_state\": %s, \
     \"transaction\": %s, \
     \"report\": %s\
     }"
    case_index
    (json_string case.tx_name)
    case.tx_height
    case.tx_fresh_id
    (json_int_list case.tx_observed_ids)
    (json_state case.tx_observed_ids case.tx_utxo)
    (json_transaction case.tx_body)
    (json_tx_report report)

let json_block_case case_index case =
  let report =
    CoqExtractedTransitionKernel.structural_block_report
      case.block_utxo case.block_txs case.block_height config case.block_fresh_id
  in
  Printf.sprintf
    "{\
     \"kind\": \"block\", \
     \"index\": %d, \
     \"name\": %s, \
     \"height\": %d, \
     \"fresh_id\": %d, \
     \"observed_ids\": %s, \
     \"pre_state\": %s, \
     \"block\": {\"transactions\": %s}, \
     \"report\": %s\
     }"
    case_index
    (json_string case.block_name)
    case.block_height
    case.block_fresh_id
    (json_int_list case.block_observed_ids)
    (json_state case.block_observed_ids case.block_utxo)
    (json_block case.block_txs)
    (json_block_report case.block_observed_ids report)

let indexed_json_cases render cases =
  cases
  |> List.mapi render
  |> String.concat ",\n    "

let () =
  Printf.printf "{\n";
  Printf.printf "  \"model\": \"transition-kernel-refinement\",\n";
  Printf.printf "  \"evidence\": \"per-case-structured-witnesses\",\n";
  Printf.printf "  \"oracle\": \"CoqExtractedTransitionKernel\",\n";
  Printf.printf "  \"rust_adapter\": \"DeployedTransitionKernel\",\n";
  Printf.printf "  \"tx_case_count\": %d,\n" (List.length tx_cases);
  Printf.printf "  \"block_case_count\": %d,\n" (List.length block_cases);
  Printf.printf "  \"projection\": \"coq_nat_outpoint_to_rust_initial_or_fresh_output_id\",\n";
  Printf.printf "  \"observed_reports\": [\"StructuralTxReport\", \"StructuralBlockReport\"],\n";
  Printf.printf "  \"cases\": {\n";
  Printf.printf "    \"transactions\": [\n    %s\n    ],\n"
    (indexed_json_cases json_tx_case tx_cases);
  Printf.printf "    \"blocks\": [\n    %s\n    ]\n"
    (indexed_json_cases json_block_case block_cases);
  Printf.printf "  }\n";
  Printf.printf "}\n"
