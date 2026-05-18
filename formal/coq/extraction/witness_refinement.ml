(* witness_refinement.ml: bounded witness-level refinement summary.
 *
 * This executable calls the Coq-extracted single-signature witness serializer,
 * byte-level parser, consensus-domain parser, and canonicality predicates over
 * a deterministic boundary matrix.
 * The Rust side computes the same transcript with src/encoding.rs. CI compares
 * the resulting JSON objects exactly.
 *
 * The matrix is intentionally structural: parser control flow depends on
 * CompactSize length decoding, exact byte counts, empty-component rejection,
 * trailing-byte rejection, and the consensus MAX_WITNESS_SIZE guard. Payload
 * bytes are deterministic representatives and are included in the transcript
 * digest, so any copied-byte divergence is observable.
 *)

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

let add_bytes d bytes =
  let d = add_nat d (List.length bytes) in
  List.fold_left add_byte d bytes

let add_trace d trace =
  let d = add_nat d (List.length trace) in
  List.fold_left add_nat d trace

let add_parse_result d result =
  match result with
  | None -> add_byte d 0
  | Some (pk, signature) ->
      let d = add_byte d 1 in
      let d = add_bytes d pk in
      add_bytes d signature

let serialize_witness =
  Golden_vectors_extracted.WitnessExtraction.extract_serialize_witness

let parse_witness =
  Golden_vectors_extracted.WitnessExtraction.extract_parse_witness

let parse_consensus_witness =
  Golden_vectors_extracted.WitnessExtraction.extract_parse_consensus_witness

let parse_witness_trace =
  Golden_vectors_extracted.WitnessExtraction.extract_parse_witness_trace

let is_canonical_witness =
  Golden_vectors_extracted.WitnessExtraction.extract_is_canonical_witness_bytes

let is_canonical_consensus_witness =
  Golden_vectors_extracted.WitnessExtraction.extract_is_canonical_consensus_witness_bytes

let byte_at seed i =
  (seed + (i * 131) + ((i / 7) * 17) + (i land 31)) land 0xff

let bytes len seed =
  let rec loop i acc =
    if i < 0 then acc else loop (i - 1) (byte_at seed i :: acc)
  in
  loop (len - 1) []

let canonical_lengths =
  [
    0; 1; 2; 3; 4; 31; 32; 33; 100; 251; 252; 253; 254; 255; 256; 512;
    1000; 1312; 2420; 7856; 8000; 12000; 15990; 15991; 15992; 15993; 15994;
    15995; 15996; 15997; 15998; 15999; 16000; 65535;
  ]

let symbolic_alphabet = [0; 1; 2; 3; 4; 31; 32; 33; 252; 253]
let symbolic_max_len = 5

let record_observation d tag witness =
  let trace, traced_result = parse_witness_trace witness in
  let d = add_byte d tag in
  let d = add_bytes d witness in
  let d = add_parse_result d (parse_witness witness) in
  let d = add_parse_result d (parse_consensus_witness witness) in
  let d = add_parse_result d traced_result in
  let d = add_trace d trace in
  let d = add_bool d (is_canonical_witness witness) in
  add_bool d (is_canonical_consensus_witness witness)

let record_canonical_case d case_index pk_len sig_len =
  let pk = bytes pk_len (0x31 + case_index) in
  let signature = bytes sig_len (0xA7 + case_index) in
  let witness = serialize_witness pk signature in
  let d = add_byte d 0xC1 in
  let d = add_nat d case_index in
  let d = add_nat d pk_len in
  let d = add_nat d sig_len in
  let d = add_bytes d pk in
  let d = add_bytes d signature in
  record_observation d 0xC2 witness

let malformed_cases () =
  let valid_small = serialize_witness [1; 2; 3] [0xAA; 0xBB] in
  [
    [];
    [0; 1; 0xAA];
    [1; 0xAA; 0];
    [10; 1; 2; 3];
    [1; 0xAA];
    [253];
    [253; 0];
    [253; 1; 0; 0xAA; 1; 0xBB];
    [1; 0xAA; 253; 1; 0; 0xBB];
    valid_small @ [255];
    [1; 0xAA; 3; 0xBB];
    [253; 253; 0; 0xAA];
    [1; 0xAA; 253; 253; 0; 0xBB];
    [254];
    [255];
  ]

let fold_canonical_matrix d =
  let case_index = ref 0 in
  List.fold_left
    (fun outer pk_len ->
      List.fold_left
        (fun inner sig_len ->
          let current = !case_index in
          incr case_index;
          record_canonical_case inner current pk_len sig_len)
        outer canonical_lengths)
    d canonical_lengths

let fold_malformed d =
  let case_index = ref 0 in
  List.fold_left
    (fun acc witness ->
      let current = !case_index in
      incr case_index;
      let acc = add_byte acc 0xE1 in
      let acc = add_nat acc current in
      record_observation acc 0xE2 witness)
    d (malformed_cases ())

let rec fold_symbolic_words len prefix f acc =
  if len = 0 then f acc (List.rev prefix)
  else
    List.fold_left
      (fun inner byte -> fold_symbolic_words (len - 1) (byte :: prefix) f inner)
      acc symbolic_alphabet

let fold_symbolic_state_space d =
  let case_index = ref 0 in
  let rec fold_len len acc =
    if len > symbolic_max_len then acc
    else
      let acc =
        fold_symbolic_words len []
          (fun inner witness ->
            let current = !case_index in
            incr case_index;
            let inner = add_byte inner 0xF1 in
            let inner = add_nat inner current in
            let inner = add_nat inner len in
            record_observation inner 0xF2 witness)
          acc
      in
      fold_len (len + 1) acc
  in
  fold_len 0 d

let rec pow base exp =
  if exp = 0 then 1 else base * pow base (exp - 1)

let symbolic_case_count () =
  let rec loop len acc =
    if len > symbolic_max_len then acc
    else loop (len + 1) (acc + pow (List.length symbolic_alphabet) len)
  in
  loop 0 0

let () =
  let canonical_length_count = List.length canonical_lengths in
  let canonical_pair_cases = canonical_length_count * canonical_length_count in
  let malformed_case_count = List.length (malformed_cases ()) in
  let symbolic_case_count = symbolic_case_count () in
  let d =
    fold_symbolic_state_space (fold_malformed (fold_canonical_matrix initial_digest))
  in
  Printf.printf "{\n";
  Printf.printf "  \"model\": \"single-sig-witness-u16-refinement-matrix\",\n";
  Printf.printf "  \"domain_min\": 0,\n";
  Printf.printf "  \"domain_max\": 65535,\n";
  Printf.printf "  \"max_consensus_witness_size\": 16000,\n";
  Printf.printf "  \"canonical_length_representatives\": %d,\n" canonical_length_count;
  Printf.printf "  \"canonical_pair_cases\": %d,\n" canonical_pair_cases;
  Printf.printf "  \"malformed_cases\": %d,\n" malformed_case_count;
  Printf.printf "  \"symbolic_alphabet_size\": %d,\n" (List.length symbolic_alphabet);
  Printf.printf "  \"symbolic_max_len\": %d,\n" symbolic_max_len;
  Printf.printf "  \"symbolic_state_cases\": %d,\n" symbolic_case_count;
  Printf.printf "  \"observed_functions\": [\"serialize_witness\", \"parse_witness\", \"parse_consensus_witness\", \"parse_witness_trace\", \"is_canonical_witness\", \"is_canonical_consensus_witness\"],\n";
  Printf.printf "  \"hash_mod_1000000007\": %d,\n" d.h1;
  Printf.printf "  \"hash_mod_1000000009\": %d\n" d.h2;
  Printf.printf "}\n"
