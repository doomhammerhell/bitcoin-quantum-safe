(* varint_refinement.ml: Exhaustive bounded varint refinement summary.
 *
 * This executable calls the Coq-extracted compact-size varint encoder/decoder
 * for every value in the current formal domain, 0..=65535, and emits a compact
 * JSON summary. The Rust side computes the same summary with src/encoding.rs;
 * CI compares the JSON objects exactly.
 *)

let modulus_1 = 1_000_000_007
let modulus_2 = 1_000_000_009
let multiplier = 16_777_619

type digest = {
  h1 : int;
  h2 : int;
}

let initial_digest = { h1 = 2_166_136_261 mod modulus_1; h2 = 2_166_136_261 mod modulus_2 }

let step_mod modulus h byte =
  ((h * multiplier) + (byte land 0xff) + 1) mod modulus

let add_byte d byte =
  { h1 = step_mod modulus_1 d.h1 byte; h2 = step_mod modulus_2 d.h2 byte }

let add_nat d n =
  let rec loop i value acc =
    if i = 8 then acc
    else loop (i + 1) (value lsr 8) (add_byte acc (value land 0xff))
  in
  loop 0 n d

let add_option_pair d result =
  match result with
  | None -> add_byte d 0
  | Some (value, consumed) ->
      let d = add_byte d 1 in
      let d = add_nat d value in
      add_nat d consumed

let encode_varint =
  Golden_vectors_extracted.WitnessExtraction.extract_encode_varint

let decode_varint =
  Golden_vectors_extracted.WitnessExtraction.extract_decode_varint

let record_encoded d n encoded =
  let d = add_byte d 0xE1 in
  let d = add_nat d n in
  let d = add_nat d (List.length encoded) in
  List.fold_left add_byte d encoded

let record_decoded d tag bytes =
  let d = add_byte d tag in
  let d = add_nat d (List.length bytes) in
  add_option_pair d (decode_varint bytes)

let rec fold_range lo hi f acc =
  if lo > hi then acc else fold_range (lo + 1) hi f (f acc lo)

let () =
  let d =
    fold_range 0 65_535
      (fun acc n ->
        let encoded = encode_varint n in
        let acc = record_encoded acc n encoded in
        let acc = record_decoded acc 0xD1 encoded in
        record_decoded acc 0xD2 (encoded @ [17; 34; 255]))
      initial_digest
  in
  let d =
    fold_range 0 252
      (fun acc n ->
        let noncanonical = [253; n land 0xff; n lsr 8] in
        record_decoded acc 0xB1 noncanonical)
      d
  in
  let d =
    List.fold_left
      (fun acc bytes -> record_decoded acc 0xB2 bytes)
      d
      [[253]; [253; 0]; [254]; [255]]
  in
  Printf.printf "{\n";
  Printf.printf "  \"model\": \"bitcoin-compact-size-u16\",\n";
  Printf.printf "  \"domain_min\": 0,\n";
  Printf.printf "  \"domain_max\": 65535,\n";
  Printf.printf "  \"encode_cases\": 65536,\n";
  Printf.printf "  \"decode_cases\": 65536,\n";
  Printf.printf "  \"trailing_decode_cases\": 65536,\n";
  Printf.printf "  \"noncanonical_fd_cases\": 253,\n";
  Printf.printf "  \"truncated_or_unsupported_cases\": 4,\n";
  Printf.printf "  \"hash_mod_1000000007\": %d,\n" d.h1;
  Printf.printf "  \"hash_mod_1000000009\": %d\n" d.h2;
  Printf.printf "}\n"
