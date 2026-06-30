(* txid_refinement.ml: PO-5 txid preimage refinement summary.
 *
 * This executable uses the Coq-extracted txid transcript serializer from
 * TxidPreimage.v. The Rust side calls `src/lib.rs::txid_preimage` on the same
 * deterministic cases; CI compares the summaries exactly.
 *)

open Txid_extracted

let modulus_1 = 1_000_000_007
let modulus_2 = 1_000_000_009
let multiplier = 16_777_619
let txid_domain_len = 17

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

let add_bytes d bytes =
  let d = add_nat d (List.length bytes) in
  List.fold_left add_byte d bytes

let add_string d value =
  let rec loop i acc =
    if i = String.length value then acc
    else loop (i + 1) (add_byte acc (Char.code value.[i]))
  in
  loop 0 (add_nat d (String.length value))

let commitment seed =
  let byte_at index =
    (seed + (index * 17) + (index / 5)) land 0xff
  in
  let rec loop index acc =
    if index < 0 then acc else loop (index - 1) (byte_at index :: acc)
  in
  loop 31 []

let outpoint seed vout =
  let byte_at index =
    (seed + (index * 29) + (index / 3)) land 0xff
  in
  let rec loop index acc =
    if index < 0 then acc else loop (index - 1) (byte_at index :: acc)
  in
  { op_txid = loop 31 []; op_vout = vout }

let tx_output script_version seed value =
  {
    txo_script_version = script_version;
    txo_commitment = commitment seed;
    txo_value = value;
  }

let input outpoint witness_seed witness_len =
  {
    txi_outpoint = outpoint;
    txi_witness = List.init witness_len (fun _ -> witness_seed);
  }

let tx_cases =
  [
    ( "empty",
      { tx_version = 2; tx_inputs = []; tx_outputs = []; tx_locktime = 0 } );
    ( "single-input-output",
      {
        tx_version = 2;
        tx_inputs = [ input (outpoint 1 0) 0xAA 2 ];
        tx_outputs = [ tx_output 2 0x10 50_000 ];
        tx_locktime = 0;
      } );
    ( "multi-input-output",
      {
        tx_version = 3;
        tx_inputs =
          [ input (outpoint 2 1) 0xBB 3; input (outpoint 3 7) 0xCC 4 ];
        tx_outputs = [ tx_output 0 0x20 25_000; tx_output 2 0x21 24_000 ];
        tx_locktime = 144;
      } );
    ( "count-delimited-many-inputs",
      {
        tx_version = 4;
        tx_inputs =
          List.init 41 (fun index -> input (outpoint index index) 0xDD 1);
        tx_outputs = [];
        tx_locktime = 500;
      } );
    ( "count-delimited-many-outputs",
      {
        tx_version = 4;
        tx_inputs = [];
        tx_outputs =
          List.init 36 (fun index -> tx_output 2 index (1_000 + index));
        tx_locktime = 500;
      } );
  ]

let record_case digest case_index (name, tx) =
  let preimage = TxidExtraction.extract_txid_preimage tx in
  let expected_len =
    txid_domain_len + 4 + 8 + (List.length tx.tx_inputs * 36) + 8
    + (List.length tx.tx_outputs * 41) + 4
  in
  let digest = add_byte digest 0xB5 in
  let digest = add_nat digest case_index in
  let digest = add_string digest name in
  let digest = add_nat digest tx.tx_version in
  let digest = add_nat digest tx.tx_locktime in
  let digest = add_nat digest (List.length tx.tx_inputs) in
  let digest = add_nat digest (List.length tx.tx_outputs) in
  let digest = add_bytes digest preimage in
  add_bool digest (List.length preimage = expected_len)

let () =
  let digest =
    List.fold_left
      (fun (digest, index) case -> (record_case digest index case, index + 1))
      (initial_digest, 0) tx_cases
    |> fst
  in
  Printf.printf "{\n";
  Printf.printf "  \"model\": \"txid-preimage-refinement\",\n";
  Printf.printf "  \"case_count\": %d,\n" (List.length tx_cases);
  Printf.printf "  \"domain_len\": %d,\n" txid_domain_len;
  Printf.printf "  \"observed_functions\": [\"txid_preimage\"],\n";
  Printf.printf "  \"hash_mod_1000000007\": %d,\n" digest.h1;
  Printf.printf "  \"hash_mod_1000000009\": %d\n" digest.h2;
  Printf.printf "}\n"
