(* transition_invariant_refinement.ml: PO-6 structural invariant witnesses.
 *
 * This harness exposes the Coq theorem boundary for UTXO-domain preservation,
 * total-value non-increase, migration monotonicity, and freeze observables.
 * The domain theorem requires a duplicate-free pre-state domain below the
 * fresh-id base; cases that violate that freshness precondition are reported as
 * explicit boundary cases rather than as theorem-covered executions.
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
      block_name = "grace-period-migrates-legacy-to-pq";
      block_height = 120;
      block_utxo = [ (30, output 0 100) ];
      block_txs = [ tx [ 30 ] [ tx_output 2 90 ] ];
      block_fresh_id = 360;
      block_observed_ids = [ 30; 360 ];
    };
    {
      block_name = "grace-period-rejects-legacy-recreation";
      block_height = 120;
      block_utxo = [ (31, output 0 100) ];
      block_txs = [ tx [ 31 ] [ tx_output 0 90 ] ];
      block_fresh_id = 370;
      block_observed_ids = [ 31; 370 ];
    };
    {
      block_name = "post-cutover-preserves-frozen-legacy-with-pq-spend";
      block_height = 180;
      block_utxo = [ (40, output 0 70); (41, output 2 50) ];
      block_txs = [ tx [ 41 ] [ tx_output 2 45 ] ];
      block_fresh_id = 380;
      block_observed_ids = [ 40; 41; 380 ];
    };
    {
      block_name = "post-cutover-rejects-frozen-legacy-spend";
      block_height = 180;
      block_utxo = [ (42, output 0 70) ];
      block_txs = [ tx [ 42 ] [ tx_output 2 70 ] ];
      block_fresh_id = 390;
      block_observed_ids = [ 42; 390 ];
    };
    {
      block_name = "post-cutover-mixed-inputs-rejected";
      block_height = 180;
      block_utxo = [ (43, output 0 40); (44, output 2 40) ];
      block_txs = [ tx [ 43; 44 ] [ tx_output 2 70 ] ];
      block_fresh_id = 400;
      block_observed_ids = [ 43; 44; 400 ];
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
    {
      block_name = "fresh-bound-precondition-fails";
      block_height = 50;
      block_utxo = [ (20, output 0 50); (400, output 2 7) ];
      block_txs = [ tx [ 20 ] [ tx_output 2 40 ] ];
      block_fresh_id = 390;
      block_observed_ids = [ 20; 390; 400 ];
    };
    {
      block_name = "fresh-id-collision-boundary";
      block_height = 50;
      block_utxo = [ (20, output 0 50); (390, output 2 7) ];
      block_txs = [ tx [ 20 ] [ tx_output 2 40 ] ];
      block_fresh_id = 390;
      block_observed_ids = [ 20 ];
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

let json_nullable_bool = function
  | None -> "null"
  | Some value -> json_bool value

let json_nullable_int = function
  | None -> "null"
  | Some value -> string_of_int value

let rec json_int_list = function
  | [] -> "[]"
  | xs -> "[" ^ String.concat ", " (List.map string_of_int xs) ^ "]"

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

let json_block txs =
  "[" ^ String.concat ", " (List.map json_transaction txs) ^ "]"

let boundary_reason freshness_precondition final_state =
  if not freshness_precondition then
    Some "fresh-id precondition false; txid/freshness collision boundary outside theorem"
  else if not (option_is_some final_state) then
    Some "block rejected; final-state preservation theorem premise not satisfied"
  else
    None

let migration_reason post_announcement final_state =
  if not post_announcement then
    Some "pre-announcement; migration monotonicity theorem premise not active"
  else if not (option_is_some final_state) then
    Some "block rejected; migration monotonicity theorem premise not satisfied"
  else
    None

let cutover_reason post_cutover final_state =
  if not post_cutover then
    Some "pre-cutover; freeze theorem premise not active"
  else if not (option_is_some final_state) then
    Some "block rejected; freeze theorem premise not satisfied"
  else
    None

let frozen_count_reason config_order post_cutover final_state =
  if not config_order then
    Some "invalid migration config ordering; frozen-count theorem premise not satisfied"
  else
    cutover_reason post_cutover final_state

let json_reason = function
  | None -> "null"
  | Some reason -> json_string reason

let json_final_state observed_ids freshness_precondition final_state =
  if freshness_precondition then
    match final_state with
    | None -> "null"
    | Some utxo -> json_state observed_ids utxo
  else
    "null"

let json_case case_index case =
  let output_count =
    TransitionExtraction.extract_block_output_count case.block_txs
  in
  let next_fresh_id = case.block_fresh_id + output_count in
  let pre_domain =
    TransitionExtraction.extract_utxo_domain case.block_utxo
  in
  let pre_total_value =
    TransitionExtraction.extract_utxo_total_value case.block_utxo
  in
  let pre_legacy_count =
    TransitionExtraction.extract_legacy_utxo_count case.block_utxo
  in
  let pre_frozen_count =
    TransitionExtraction.extract_frozen_utxo_count case.block_height config case.block_utxo
  in
  let spent_input_ids =
    TransitionExtraction.extract_block_input_outpoints case.block_txs
  in
  let post_announcement =
    config.announcement_height <= case.block_height
  in
  let post_cutover =
    config.cutover_height <= case.block_height
  in
  let config_order =
    config.announcement_height <= config.cutover_height
  in
  let pre_domain_unique =
    TransitionExtraction.extract_domain_has_no_duplicates case.block_utxo
  in
  let pre_domain_below_fresh =
    TransitionExtraction.extract_domain_below_bool case.block_utxo case.block_fresh_id
  in
  let freshness_precondition = pre_domain_unique && pre_domain_below_fresh in
  let valid_block =
    TransitionExtraction.extract_valid_block_structural
      case.block_utxo case.block_txs case.block_height config case.block_fresh_id
  in
  let final_state =
    TransitionExtraction.extract_apply_valid_block_structural
      case.block_utxo case.block_txs case.block_height config case.block_fresh_id
  in
  let observed_final =
    if freshness_precondition then final_state else None
  in
  let final_domain_unique =
    match observed_final with
    | None -> None
    | Some utxo -> Some (TransitionExtraction.extract_domain_has_no_duplicates utxo)
  in
  let final_domain_below_next_fresh =
    match observed_final with
    | None -> None
    | Some utxo -> Some (TransitionExtraction.extract_domain_below_bool utxo next_fresh_id)
  in
  let spent_inputs_absent =
    match observed_final with
    | None -> None
    | Some utxo -> Some (TransitionExtraction.extract_spent_inputs_absent_bool utxo case.block_txs)
  in
  let final_total_value =
    match observed_final with
    | None -> None
    | Some utxo -> Some (TransitionExtraction.extract_utxo_total_value utxo)
  in
  let final_total_value_lte_pre =
    match final_total_value with
    | None -> None
    | Some total -> Some (total <= pre_total_value)
  in
  let final_legacy_count =
    match final_state with
    | None -> None
    | Some utxo -> Some (TransitionExtraction.extract_legacy_utxo_count utxo)
  in
  let final_legacy_count_lte_pre_after_announcement =
    if post_announcement then
      match final_legacy_count with
      | None -> None
      | Some count -> Some (count <= pre_legacy_count)
    else
      None
  in
  let final_frozen_count =
    match final_state with
    | None -> None
    | Some utxo ->
        Some
          (TransitionExtraction.extract_frozen_utxo_count
            case.block_height config utxo)
  in
  let final_frozen_count_lte_pre_after_cutover =
    if config_order && post_cutover then
      match final_frozen_count with
      | None -> None
      | Some count -> Some (count <= pre_frozen_count)
    else
      None
  in
  let accepted_inputs_pq_or_missing =
    TransitionExtraction.extract_accepted_block_inputs_pq_or_missing
      case.block_utxo case.block_txs case.block_height config case.block_fresh_id
  in
  let accepted_inputs_pq_or_missing_after_cutover =
    if post_cutover then Some accepted_inputs_pq_or_missing else None
  in
  let theorem_applicable = freshness_precondition && option_is_some final_state in
  let theorem_conclusion_holds =
    match final_domain_unique, final_domain_below_next_fresh with
    | Some true, Some true when theorem_applicable -> Some true
    | Some _, Some _ when theorem_applicable -> Some false
    | _, _ -> None
  in
  let value_theorem_conclusion_holds =
    match final_total_value_lte_pre with
    | Some true when theorem_applicable -> Some true
    | Some _ when theorem_applicable -> Some false
    | _ -> None
  in
  let migration_theorem_applicable =
    post_announcement && option_is_some final_state
  in
  let migration_theorem_conclusion_holds =
    match final_legacy_count_lte_pre_after_announcement with
    | Some true when migration_theorem_applicable -> Some true
    | Some _ when migration_theorem_applicable -> Some false
    | _ -> None
  in
  let freeze_theorem_applicable =
    post_cutover && option_is_some final_state
  in
  let freeze_theorem_conclusion_holds =
    if freeze_theorem_applicable then Some accepted_inputs_pq_or_missing else None
  in
  let frozen_count_theorem_applicable =
    config_order && post_cutover && option_is_some final_state
  in
  let frozen_count_theorem_conclusion_holds =
    match final_frozen_count_lte_pre_after_cutover with
    | Some true when frozen_count_theorem_applicable -> Some true
    | Some _ when frozen_count_theorem_applicable -> Some false
    | _ -> None
  in
  Printf.sprintf
    "{\
     \"kind\": \"block-invariant\", \
     \"index\": %d, \
     \"name\": %s, \
     \"height\": %d, \
     \"fresh_id\": %d, \
     \"next_fresh_id\": %d, \
     \"observed_ids\": %s, \
     \"pre_domain\": %s, \
     \"pre_total_value\": %d, \
     \"pre_legacy_count\": %d, \
     \"pre_frozen_count\": %d, \
     \"pre_state\": %s, \
     \"block\": {\"transactions\": %s}, \
     \"spent_input_ids\": %s, \
     \"preconditions\": {\
       \"pre_domain_unique\": %s, \
       \"pre_domain_below_fresh\": %s, \
       \"fresh_id_assumption_holds\": %s\
     }, \
     \"result\": {\
       \"valid_block\": %s, \
       \"final_state\": %s, \
       \"final_domain_unique\": %s, \
       \"final_domain_below_next_fresh\": %s, \
       \"spent_inputs_absent\": %s, \
       \"final_total_value\": %s, \
       \"final_total_value_lte_pre\": %s, \
       \"final_legacy_count\": %s, \
       \"final_legacy_count_lte_pre_after_announcement\": %s, \
       \"final_frozen_count\": %s, \
       \"final_frozen_count_lte_pre_after_cutover\": %s, \
       \"accepted_inputs_pq_or_missing\": %s, \
       \"accepted_inputs_pq_or_missing_after_cutover\": %s\
     }, \
     \"theorem\": {\
       \"name\": \"apply_valid_block_structural_preserves_domain_nodup\", \
       \"applicable\": %s, \
       \"conclusion_holds\": %s, \
       \"non_applicability_reason\": %s\
     }, \
     \"value_theorem\": {\
       \"name\": \"apply_valid_block_structural_preserves_total_value\", \
       \"applicable\": %s, \
       \"conclusion_holds\": %s, \
       \"non_applicability_reason\": %s\
     }, \
     \"migration_theorem\": {\
       \"name\": \"apply_valid_block_structural_legacy_count_nonincreasing_after_announcement\", \
       \"applicable\": %s, \
       \"conclusion_holds\": %s, \
       \"non_applicability_reason\": %s\
     }, \
     \"freeze_theorem\": {\
       \"name\": \"apply_valid_block_structural_inputs_pq_after_cutover\", \
       \"applicable\": %s, \
       \"conclusion_holds\": %s, \
       \"non_applicability_reason\": %s\
     }, \
     \"frozen_count_theorem\": {\
       \"name\": \"apply_valid_block_structural_frozen_count_nonincreasing_after_cutover\", \
       \"applicable\": %s, \
       \"conclusion_holds\": %s, \
       \"non_applicability_reason\": %s\
     }\
     }"
    case_index
    (json_string case.block_name)
    case.block_height
    case.block_fresh_id
    next_fresh_id
    (json_int_list case.block_observed_ids)
    (json_int_list pre_domain)
    pre_total_value
    pre_legacy_count
    pre_frozen_count
    (json_state case.block_observed_ids case.block_utxo)
    (json_block case.block_txs)
    (json_int_list spent_input_ids)
    (json_bool pre_domain_unique)
    (json_bool pre_domain_below_fresh)
    (json_bool freshness_precondition)
    (json_bool valid_block)
    (json_final_state case.block_observed_ids freshness_precondition final_state)
    (json_nullable_bool final_domain_unique)
    (json_nullable_bool final_domain_below_next_fresh)
    (json_nullable_bool spent_inputs_absent)
    (json_nullable_int final_total_value)
    (json_nullable_bool final_total_value_lte_pre)
    (json_nullable_int final_legacy_count)
    (json_nullable_bool final_legacy_count_lte_pre_after_announcement)
    (json_nullable_int final_frozen_count)
    (json_nullable_bool final_frozen_count_lte_pre_after_cutover)
    (json_bool accepted_inputs_pq_or_missing)
    (json_nullable_bool accepted_inputs_pq_or_missing_after_cutover)
    (json_bool theorem_applicable)
    (json_nullable_bool theorem_conclusion_holds)
    (json_reason (boundary_reason freshness_precondition final_state))
    (json_bool theorem_applicable)
    (json_nullable_bool value_theorem_conclusion_holds)
    (json_reason (boundary_reason freshness_precondition final_state))
    (json_bool migration_theorem_applicable)
    (json_nullable_bool migration_theorem_conclusion_holds)
    (json_reason (migration_reason post_announcement final_state))
    (json_bool freeze_theorem_applicable)
    (json_nullable_bool freeze_theorem_conclusion_holds)
    (json_reason (cutover_reason post_cutover final_state))
    (json_bool frozen_count_theorem_applicable)
    (json_nullable_bool frozen_count_theorem_conclusion_holds)
    (json_reason (frozen_count_reason config_order post_cutover final_state))

let indexed_json_cases render cases =
  cases
  |> List.mapi render
  |> String.concat ",\n"

let () =
  Printf.printf "{\n";
  Printf.printf "  \"model\": \"utxo-domain-value-migration-freeze-invariant-refinement\",\n";
  Printf.printf "  \"evidence\": \"per-case-structured-invariant-witnesses\",\n";
  Printf.printf "  \"proof_boundary\": \"Coq theorems for domain preservation, value non-increase, legacy-output non-increase after announcement, PQ-only accepted inputs after cutover, and frozen-count non-increase after cutover under their explicit premises\",\n";
  Printf.printf "  \"case_count\": %d,\n" (List.length block_cases);
  Printf.printf "  \"cases\": [\n%s\n  ]\n" (indexed_json_cases json_case block_cases);
  Printf.printf "}\n"
