(* sighash_refinement.ml: PO-4 sighash transcript refinement summary.
 *
 * This executable uses Coq-extracted deterministic serializers from
 * SighashV2.v. SHA-256 remains axiomatized in Coq; therefore the refinement
 * boundary is the byte transcript around SHA-256: outpoints, outputs,
 * spent-output context, and final preimage assembly with supplied 32-byte
 * sub-hashes.
 *)

open Sighash_extracted

let modulus_1 = 1_000_000_007
let modulus_2 = 1_000_000_009
let multiplier = 16_777_619
let preimage_len = 119

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

let byte_at seed i =
  (seed + (i * 131) + ((i / 7) * 17) + (i land 31)) land 0xff

let bytes len seed =
  let rec loop i acc =
    if i < 0 then acc else loop (i - 1) (byte_at seed i :: acc)
  in
  loop (len - 1) []

let bytes32 seed =
  bytes 32 seed

let input txid_seed vout witness_seed witness_len =
  {
    txi_outpoint = { op_txid = bytes32 txid_seed; op_vout = vout };
    txi_witness = bytes witness_len witness_seed;
  }

let tx_output script_version commitment_seed value =
  {
    txo_script_version = script_version;
    txo_commitment = bytes32 commitment_seed;
    txo_value = value;
  }

let spent_output script_version commitment_seed value =
  {
    so_script_version = script_version;
    so_commitment = bytes32 commitment_seed;
    so_value = value;
  }

let serialize_outpoints tx =
  List.concat
    (List.map
       (fun input ->
         SighashExtraction.extract_serialize_outpoint input.txi_outpoint)
       tx.tx_inputs)

let serialize_outputs tx =
  List.concat
    (List.map SighashExtraction.extract_serialize_output tx.tx_outputs)

type case = {
  name : string;
  tx : transaction;
  input_index : int;
  spent : spentOutput;
  hash_outpoints : int list;
  hash_outputs : int list;
}

let cases =
  [
    {
      name = "single-input-single-output";
      tx =
        {
          tx_version = 2;
          tx_inputs = [ input 0x10 0 0xA0 1 ];
          tx_outputs = [ tx_output 2 0x20 1_000 ];
          tx_locktime = 0;
        };
      input_index = 0;
      spent = spent_output 2 0x30 2_000;
      hash_outpoints = bytes32 0x40;
      hash_outputs = bytes32 0x50;
    };
    {
      name = "two-inputs-two-outputs-index-one";
      tx =
        {
          tx_version = 2;
          tx_inputs = [ input 0x11 0 0xA1 2; input 0x12 1 0xA2 3 ];
          tx_outputs = [ tx_output 2 0x21 50_000; tx_output 1 0x22 25_000 ];
          tx_locktime = 100;
        };
      input_index = 1;
      spent = spent_output 2 0x31 75_000;
      hash_outpoints = bytes32 0x41;
      hash_outputs = bytes32 0x51;
    };
    {
      name = "little-endian-boundaries";
      tx =
        {
          tx_version = 0xA1B2_C3D4;
          tx_inputs =
            [ input 0x13 0xDEAD_BEEF 0xA3 4; input 0x14 0x0102_0304 0xA4 5 ];
          tx_outputs = [ tx_output 255 0x23 281_474_976_710_655 ];
          tx_locktime = 0xFEDC_BA98;
        };
      input_index = 0;
      spent = spent_output 254 0x32 9_007_199_254_740_991;
      hash_outpoints = bytes32 0x42;
      hash_outputs = bytes32 0x52;
    };
    {
      name = "zero-outputs";
      tx =
        {
          tx_version = 0;
          tx_inputs = [ input 0x15 2 0xA5 0 ];
          tx_outputs = [];
          tx_locktime = 42;
        };
      input_index = 0;
      spent = spent_output 0 0x33 0;
      hash_outpoints = bytes32 0x43;
      hash_outputs = bytes32 0x53;
    };
    {
      name = "witness-bytes-excluded";
      tx =
        {
          tx_version = 3;
          tx_inputs = [ input 0x16 7 0xA6 128; input 0x17 8 0xA7 64 ];
          tx_outputs = [ tx_output 2 0x24 4_000_000 ];
          tx_locktime = 500_000;
        };
      input_index = 1;
      spent = spent_output 2 0x34 4_500_000;
      hash_outpoints = bytes32 0x44;
      hash_outputs = bytes32 0x54;
    };
  ]

let record_case d case_index case =
  let outpoints = serialize_outpoints case.tx in
  let outputs = serialize_outputs case.tx in
  let spent = SighashExtraction.extract_serialize_spent_output case.spent in
  let preimage =
    SighashExtraction.extract_sighash_preimage_from_hashes case.tx case.input_index
      case.spent case.hash_outpoints case.hash_outputs
  in
  let d = add_byte d 0xA1 in
  let d = add_nat d case_index in
  let d = add_string d case.name in
  let d = add_nat d case.tx.tx_version in
  let d = add_nat d case.tx.tx_locktime in
  let d = add_nat d case.input_index in
  let d = add_nat d (List.length case.tx.tx_inputs) in
  let d = add_nat d (List.length case.tx.tx_outputs) in
  let d = add_bytes d outpoints in
  let d = add_bytes d outputs in
  let d = add_bytes d spent in
  let d = add_bytes d case.hash_outpoints in
  let d = add_bytes d case.hash_outputs in
  let d = add_bytes d preimage in
  add_bool d (List.length preimage = preimage_len)

let () =
  let d =
    List.fold_left
      (fun (digest, index) case -> (record_case digest index case, index + 1))
      (initial_digest, 0) cases
    |> fst
  in
  Printf.printf "{\n";
  Printf.printf "  \"model\": \"sighash-v2-transcript-refinement\",\n";
  Printf.printf "  \"case_count\": %d,\n" (List.length cases);
  Printf.printf "  \"preimage_len\": %d,\n" preimage_len;
  Printf.printf "  \"observed_functions\": [\"serialize_sighash_outpoints\", \"serialize_sighash_outputs\", \"serialize_sighash_spent_output\", \"sighash_v2_preimage_with_hashes\"],\n";
  Printf.printf "  \"hash_mod_1000000007\": %d,\n" d.h1;
  Printf.printf "  \"hash_mod_1000000009\": %d\n" d.h2;
  Printf.printf "}\n"
