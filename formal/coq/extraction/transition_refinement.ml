(* transition_refinement.ml: PO-5 UTXO transition refinement summary.
 *
 * This executable uses Coq-extracted structural transition functions from
 * UTXOTransitions.v. The comparison boundary is an explicit projection:
 * Coq outpoint n corresponds to Rust's initial synthetic outpoint n or to the
 * nth fresh output assigned by the harness for a transaction. SHA-256 txid
 * collision resistance, Rust HashMap internals, cryptographic witness
 * verification, and compiler correctness remain outside this artifact.
 *)

open Transition_extracted

let modulus_1 = 1_000_000_007
let modulus_2 = 1_000_000_009
let multiplier = 16_777_619

type digest = {
  h1 : int;
  h2 : int;
}

let initial_digest =
  { h1 = 2_166_136_261 mod modulus_1; h2 = 2_166_136_261 mod modulus_2 }

let step_mod modulus h byte =
  ((h * multiplier) + (byte land 0xff) + 1) mod modulus

let add_byte d byte =
  { h1 = step_mod modulus_1 d.h1 byte; h2 = step_mod modulus_2 d.h2 byte }

let add_bool d value =
  add_byte d (if value then 1 else 0)

let add_nat d n =
  let rec loop i value acc =
    if i = 8 then acc
    else loop (i + 1) (value lsr 8) (add_byte acc (value land 0xff))
  in
  loop 0 n d

let add_string d value =
  let rec loop i acc =
    if i = String.length value then acc
    else loop (i + 1) (add_byte acc (Char.code value.[i]))
  in
  loop 0 (add_nat d (String.length value))

let add_option_nat d = function
  | None -> add_bool d false
  | Some n -> add_nat (add_bool d true) n

let add_output d = function
  | None -> add_bool d false
  | Some output ->
      let d = add_bool d true in
      let d = add_nat d output.script_version in
      add_nat d output.value

let add_state d observed_ids utxo =
  let d = add_nat d (List.length observed_ids) in
  List.fold_left
    (fun acc id ->
      let acc = add_nat acc id in
      add_output acc (TransitionExtraction.extract_lookup utxo id))
    d observed_ids

let output script_version value =
  { script_version; value }

let tx_output tx_script_version tx_value =
  { tx_script_version; tx_value }

let tx inputs outputs =
  { inputs; outputs }

let config =
  { announcement_height = 100; cutover_height = 160 }

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

type cost_case = {
  cost_name : string;
  cost_shapes : (int list * int) list;
}

let cost_cases =
  [
    { cost_name = "empty-cost-block"; cost_shapes = [] };
    { cost_name = "single-small-cost"; cost_shapes = [ ([ 0 ], 1) ] };
    { cost_name = "multi-witness-cost"; cost_shapes = [ ([ 3; 5 ], 2); ([], 0) ] };
    { cost_name = "exact-cost-limit"; cost_shapes = [ ([ 3_999_816 ], 0) ] };
    { cost_name = "over-cost-limit"; cost_shapes = [ ([ 4_000_000 ], 0) ] };
  ]

let add_final_state d observed_ids = function
  | None -> add_bool d false
  | Some utxo -> add_state (add_bool d true) observed_ids utxo

let record_tx_case d case_index case =
  let d = add_byte d 0xB1 in
  let d = add_nat d case_index in
  let d = add_string d case.tx_name in
  let d = add_nat d case.tx_height in
  let d = add_nat d case.tx_fresh_id in
  let d = add_state d case.tx_observed_ids case.tx_utxo in
  let d = add_bool d (TransitionExtraction.extract_has_duplicate_inputs case.tx_body) in
  let d =
    add_option_nat d
      (TransitionExtraction.extract_sum_input_values case.tx_utxo case.tx_body.inputs)
  in
  let d =
    add_nat d (TransitionExtraction.extract_sum_output_values case.tx_body.outputs)
  in
  let d =
    add_bool d
      (TransitionExtraction.extract_check_migration_rules_structural
         case.tx_height case.tx_body case.tx_utxo config)
  in
  let d =
    add_bool d
      (TransitionExtraction.extract_check_no_frozen_inputs_structural
         case.tx_height case.tx_body case.tx_utxo config)
  in
  let d =
    add_bool d
      (TransitionExtraction.extract_valid_tx_structural
         case.tx_utxo case.tx_body case.tx_height config)
  in
  let d = add_nat d (TransitionExtraction.extract_cost_tx_structural case.tx_body) in
  let post =
    TransitionExtraction.extract_delta_tx case.tx_utxo case.tx_body case.tx_fresh_id
  in
  add_state d case.tx_observed_ids post

let record_block_case d case_index case =
  let d = add_byte d 0xB2 in
  let d = add_nat d case_index in
  let d = add_string d case.block_name in
  let d = add_nat d case.block_height in
  let d = add_nat d case.block_fresh_id in
  let d = add_state d case.block_observed_ids case.block_utxo in
  let d =
    add_bool d
      (TransitionExtraction.extract_valid_block_transitions_structural
         case.block_utxo case.block_txs case.block_height config case.block_fresh_id)
  in
  let d =
    add_bool d
      (TransitionExtraction.extract_check_block_cost_structural case.block_txs)
  in
  let d =
    add_bool d
      (TransitionExtraction.extract_valid_block_structural
         case.block_utxo case.block_txs case.block_height config case.block_fresh_id)
  in
  let transition_result =
    TransitionExtraction.extract_apply_block_transitions_structural
      case.block_utxo case.block_txs case.block_height config case.block_fresh_id
  in
  let valid_result =
    TransitionExtraction.extract_apply_valid_block_structural
      case.block_utxo case.block_txs case.block_height config case.block_fresh_id
  in
  let d = add_final_state d case.block_observed_ids transition_result in
  add_final_state d case.block_observed_ids
    valid_result

let record_cost_case d case_index case =
  let d = add_byte d 0xB3 in
  let d = add_nat d case_index in
  let d = add_string d case.cost_name in
  let d = add_nat d (TransitionExtraction.extract_block_cost case.cost_shapes) in
  let d =
    add_bool d (TransitionExtraction.extract_check_block_cost_bool case.cost_shapes)
  in
  List.fold_left
    (fun acc (witness_lens, num_outputs) ->
      let acc = add_nat acc (List.length witness_lens) in
      let acc = List.fold_left add_nat acc witness_lens in
      let acc = add_nat acc num_outputs in
      let acc =
        add_nat acc (TransitionExtraction.extract_cost_tx witness_lens num_outputs)
      in
      add_nat acc
        (TransitionExtraction.extract_weight_tx
           (List.length witness_lens) witness_lens num_outputs))
    d case.cost_shapes

let fold_cases record cases digest =
  List.fold_left
    (fun (d, index) case -> (record d index case, index + 1))
    (digest, 0) cases
  |> fst

let () =
  let d = fold_cases record_tx_case tx_cases initial_digest in
  let d = fold_cases record_block_case block_cases d in
  let d = fold_cases record_cost_case cost_cases d in
  Printf.printf "{\n";
  Printf.printf "  \"model\": \"utxo-transition-refinement\",\n";
  Printf.printf "  \"tx_case_count\": %d,\n" (List.length tx_cases);
  Printf.printf "  \"block_case_count\": %d,\n" (List.length block_cases);
  Printf.printf "  \"cost_case_count\": %d,\n" (List.length cost_cases);
  Printf.printf "  \"projection\": \"coq_nat_outpoint_to_rust_initial_or_fresh_output_id\",\n";
  Printf.printf "  \"observed_functions\": [\"valid_tx_structural\", \"delta_tx\", \"apply_block_transitions_structural\", \"apply_valid_block_structural\", \"valid_block_structural\", \"cost_tx\", \"check_block_cost\"],\n";
  Printf.printf "  \"hash_mod_1000000007\": %d,\n" d.h1;
  Printf.printf "  \"hash_mod_1000000009\": %d\n" d.h2;
  Printf.printf "}\n"
