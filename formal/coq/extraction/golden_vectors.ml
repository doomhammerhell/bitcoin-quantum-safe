(* golden_vectors.ml: Golden test vector generator for PO-8 verification
 *
 * This executable produces canonical test vectors that must match the Rust
 * implementation byte-for-byte. The output is JSON-formatted for CI comparison.
 *
 * Copyright (c) 2026 Mayckon Giovani. MIT License.
 *)

(* Byte utilities *)
let hex_of_byte n =
  Printf.sprintf "%02x" (n land 0xFF)

let string_of_bytes bytes =
  String.concat "" (List.map hex_of_byte bytes)

(* Bitcoin compact-size varint encoding *)
let encode_varint (n : int) : int list =
  if n <= 252 then
    [n]
  else if n <= 0xFFFF then
    [0xFD; n land 0xFF; (n lsr 8) land 0xFF]
  else if n <= 0xFFFFFFFF then
    [0xFE; n land 0xFF; (n lsr 8) land 0xFF; (n lsr 16) land 0xFF; (n lsr 24) land 0xFF]
  else
    [0xFF; n land 0xFF; (n lsr 8) land 0xFF; (n lsr 16) land 0xFF; (n lsr 24) land 0xFF;
     (n lsr 32) land 0xFF; (n lsr 40) land 0xFF; (n lsr 48) land 0xFF; (n lsr 56) land 0xFF]

(* Witness serialization: pk_len || pk || sig_len || sig *)
let serialize_witness (pk : int list) (signature : int list) : int list =
  let pk_len = encode_varint (List.length pk) in
  let sig_len = encode_varint (List.length signature) in
  pk_len @ pk @ sig_len @ signature

(* Repeat element n times *)
let rec repeat x n =
  if n <= 0 then [] else x :: repeat x (n - 1)

(* Test cases *)

(* Case 1: Small witness (single-byte varints) *)
let test_pk_small = [0xAB; 0xCD; 0xEF] (* 3 bytes *)
let test_sig_small = [0x12; 0x34] (* 2 bytes *)

(* Case 2: ML-DSA-44 sized witness *)
(* pk_len = 1312 requires 0xFD prefix: 0xFD 0x20 0x05 (little-endian) *)
let test_pk_ml_dsa_44 = repeat 0x42 1312
let test_sig_ml_dsa_44 = repeat 0x99 2420

(* Case 3: SLH-DSA-128s sized witness *)
(* pk_len = 32 (single byte), sig_len = 7856 requires 0xFD prefix *)
let test_pk_slh_dsa = repeat 0x55 32
let test_sig_slh_dsa = repeat 0x77 7856

(* Case 4: Empty witness (edge case) *)
let test_pk_empty = []
let test_sig_empty = []

(* Case 5: Boundary values *)
(* Exactly 253 bytes (largest single-byte varint) *)
let test_pk_253 = repeat 0xAA 253
let test_sig_253 = repeat 0xBB 253

(* Exactly 254 bytes (smallest two-byte varint) *)
let test_pk_254 = repeat 0xCC 254
let test_sig_254 = repeat 0xDD 254

(* Exactly 65535 bytes (largest two-byte varint) *)
let test_pk_65535 = repeat 0xEE 65535
let test_sig_1 = [0xFF]

(* JSON output helper *)
let print_json_vector name pk signature witness =
  Printf.printf "  {\n";
  Printf.printf "    \"name\": \"%s\",\n" name;
  Printf.printf "    \"pk_len\": %d,\n" (List.length pk);
  Printf.printf "    \"pk\": \"%s\",\n" (string_of_bytes pk);
  Printf.printf "    \"sig_len\": %d,\n" (List.length signature);
  Printf.printf "    \"sig\": \"%s\",\n" (string_of_bytes signature);
  Printf.printf "    \"witness\": \"%s\"\n" (string_of_bytes witness);
  Printf.printf "  }"

(* Main *)
let () =
  Printf.printf "[\n";

  (* Vector 1: Small *)
  let w1 = serialize_witness test_pk_small test_sig_small in
  print_json_vector "small" test_pk_small test_sig_small w1;
  Printf.printf ",\n";

  (* Vector 2: ML-DSA-44 sized *)
  let w2 = serialize_witness test_pk_ml_dsa_44 test_sig_ml_dsa_44 in
  print_json_vector "ml_dsa_44" test_pk_ml_dsa_44 test_sig_ml_dsa_44 w2;
  Printf.printf ",\n";

  (* Vector 3: SLH-DSA-128s sized *)
  let w3 = serialize_witness test_pk_slh_dsa test_sig_slh_dsa in
  print_json_vector "slh_dsa_128s" test_pk_slh_dsa test_sig_slh_dsa w3;
  Printf.printf ",\n";

  (* Vector 4: Empty *)
  let w4 = serialize_witness test_pk_empty test_sig_empty in
  print_json_vector "empty" test_pk_empty test_sig_empty w4;
  Printf.printf ",\n";

  (* Vector 5: Exactly 253 bytes (boundary) *)
  let w5 = serialize_witness test_pk_253 test_sig_253 in
  print_json_vector "boundary_253" test_pk_253 test_sig_253 w5;
  Printf.printf ",\n";

  (* Vector 6: Exactly 254 bytes (boundary) *)
  let w6 = serialize_witness test_pk_254 test_sig_254 in
  print_json_vector "boundary_254" test_pk_254 test_sig_254 w6;
  Printf.printf ",\n";

  (* Vector 7: Large boundary within the Coq u16 varint model *)
  let w7 = serialize_witness test_pk_65535 test_sig_1 in
  print_json_vector "large_65535" test_pk_65535 test_sig_1 w7;
  Printf.printf "\n";
  Printf.printf "]\n";
