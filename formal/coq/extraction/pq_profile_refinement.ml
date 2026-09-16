(* pq_profile_refinement.ml: PQ signature-suite profile refinement summary.
 *
 * This executable formats the Coq-extracted PQProfile boundary as JSON. The
 * Rust side emits the same schema from src/pq_profile.rs; CI compares both
 * objects exactly and the release validator records source/binary hashes.
 *)

let json_bool value =
  if value then "true" else "false"

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

let scheme_name = function
  | 1 -> "ML-DSA-44"
  | 2 -> "SLH-DSA-128s"
  | n -> Printf.sprintf "unknown-scheme-%d" n

let standard_name = function
  | 204 -> "FIPS 204"
  | 205 -> "FIPS 205"
  | n -> Printf.sprintf "unknown-standard-%d" n

let role_name = function
  | 1 -> "primary_consensus"
  | 2 -> "conservative_fallback"
  | n -> Printf.sprintf "unknown-role-%d" n

let assumption_family_name = function
  | 1 -> "module_lattice"
  | 2 -> "hash_based"
  | n -> Printf.sprintf "unknown-assumption-%d" n

let bool_of_int = function
  | 0 -> false
  | _ -> true

let json_scheme_code_list codes =
  "["
  ^ String.concat ", " (List.map (fun code -> json_string (scheme_name code)) codes)
  ^ "]"

type profile = {
  scheme_code : int;
  standard_code : int;
  role_code : int;
  assumption_family_code : int;
  target_quantum_security_bits : int;
  public_key_len : int;
  signature_len : int;
  witness_size : int;
  fits_consensus_witness_cap : bool;
  implemented_verifier : bool;
  consensus_enabled : bool;
  primary : bool;
  fallback : bool;
}

let profile_of_row = function
  | [
      scheme_code;
      standard_code;
      role_code;
      assumption_family_code;
      target_quantum_security_bits;
      public_key_len;
      signature_len;
      witness_size;
      fits_consensus_witness_cap;
      implemented_verifier;
      consensus_enabled;
      primary;
      fallback;
    ] ->
      {
        scheme_code;
        standard_code;
        role_code;
        assumption_family_code;
        target_quantum_security_bits;
        public_key_len;
        signature_len;
        witness_size;
        fits_consensus_witness_cap = bool_of_int fits_consensus_witness_cap;
        implemented_verifier = bool_of_int implemented_verifier;
        consensus_enabled = bool_of_int consensus_enabled;
        primary = bool_of_int primary;
        fallback = bool_of_int fallback;
      }
  | row ->
      invalid_arg
        (Printf.sprintf "unexpected PQ profile row width: %d" (List.length row))

let json_profile p =
  Printf.sprintf
    "{\n\
    \      \"scheme\": %s,\n\
    \      \"standard\": %s,\n\
    \      \"role\": %s,\n\
    \      \"assumption_family\": %s,\n\
    \      \"target_quantum_security_bits\": %d,\n\
    \      \"public_key_len\": %d,\n\
    \      \"signature_len\": %d,\n\
    \      \"witness_size\": %d,\n\
    \      \"fits_consensus_witness_cap\": %s,\n\
    \      \"implemented_verifier\": %s,\n\
    \      \"consensus_enabled\": %s,\n\
    \      \"primary\": %s,\n\
    \      \"fallback\": %s\n\
    \    }"
    (json_string (scheme_name p.scheme_code))
    (json_string (standard_name p.standard_code))
    (json_string (role_name p.role_code))
    (json_string (assumption_family_name p.assumption_family_code))
    p.target_quantum_security_bits
    p.public_key_len
    p.signature_len
    p.witness_size
    (json_bool p.fits_consensus_witness_cap)
    (json_bool p.implemented_verifier)
    (json_bool p.consensus_enabled)
    (json_bool p.primary)
    (json_bool p.fallback)

let json_profiles profiles =
  "[\n    "
  ^ String.concat ",\n    " (List.map json_profile profiles)
  ^ "\n  ]"

let () =
  let open Pq_profile_extracted.PQProfileExtraction in
  let profiles = List.map profile_of_row extract_profile_rows in
  Printf.printf "{\n";
  Printf.printf "  \"model\": \"pq-signature-profile-refinement\",\n";
  Printf.printf "  \"profile_count\": %d,\n" (List.length profiles);
  Printf.printf "  \"max_consensus_witness_size\": 16000,\n";
  Printf.printf "  \"profiles\": %s,\n" (json_profiles profiles);
  Printf.printf "  \"primary_scheme\": %s,\n"
    (json_string (scheme_name extract_primary_scheme_code));
  Printf.printf "  \"fallback_scheme\": %s,\n"
    (json_string (scheme_name extract_fallback_scheme_code));
  Printf.printf "  \"implemented_schemes\": %s,\n"
    (json_scheme_code_list extract_implemented_scheme_codes);
  Printf.printf "  \"consensus_enabled_schemes\": %s,\n"
    (json_scheme_code_list extract_consensus_enabled_scheme_codes);
  Printf.printf "  \"properties\": {\n";
  Printf.printf "    \"standards_distinct\": %s,\n"
    (json_bool extract_standards_distinct);
  Printf.printf "    \"assumption_families_distinct\": %s,\n"
    (json_bool extract_assumptions_distinct);
  Printf.printf "    \"tracked_profiles_fit_current_consensus_cap\": %s,\n"
    (json_bool extract_all_profiles_fit_cap);
  Printf.printf "    \"consensus_enabled_exactly_primary\": %s,\n"
    (json_bool extract_consensus_enabled_exactly_primary);
  Printf.printf "    \"active_suite_standards_aligned\": %s\n"
    (json_bool extract_active_suite_standards_aligned);
  Printf.printf "  }\n";
  Printf.printf "}\n"
