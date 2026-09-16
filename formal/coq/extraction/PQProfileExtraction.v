(* PQProfileExtraction: extraction-facing wrappers for the PQ suite profile.
 *
 * This exposes the machine-checked profile/activation boundary from
 * PQProfile.v as compact rows that can be compared against the deployed Rust
 * profile implementation.
 *)

From Coq Require Import Extraction.
From Coq Require Import Bool.
From Coq Require Import List.
Import ListNotations.

From BitcoinPQ Require Import PQProfile.

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
Extract Constant Nat.leb => "( <= )".

Definition all_signature_schemes : list pq_signature_scheme :=
  [ML_DSA_44; SLH_DSA_128S].

Definition bool_to_nat (b : bool) : nat :=
  if b then 1 else 0.

Definition scheme_eqb (a b : pq_signature_scheme) : bool :=
  match a, b with
  | ML_DSA_44, ML_DSA_44 => true
  | SLH_DSA_128S, SLH_DSA_128S => true
  | _, _ => false
  end.

Definition standard_eqb (a b : pq_standard) : bool :=
  match a, b with
  | FIPS_204, FIPS_204 => true
  | FIPS_205, FIPS_205 => true
  | _, _ => false
  end.

Definition assumption_family_eqb (a b : assumption_family) : bool :=
  match a, b with
  | Module_Lattice, Module_Lattice => true
  | Hash_Based, Hash_Based => true
  | _, _ => false
  end.

Definition scheme_code (s : pq_signature_scheme) : nat :=
  match s with
  | ML_DSA_44 => 1
  | SLH_DSA_128S => 2
  end.

Definition standard_code (s : pq_signature_scheme) : nat :=
  match scheme_standard s with
  | FIPS_204 => 204
  | FIPS_205 => 205
  end.

Definition role_code (s : pq_signature_scheme) : nat :=
  if scheme_eqb s primary_signature_scheme then 1 else 2.

Definition assumption_family_code (s : pq_signature_scheme) : nat :=
  match scheme_assumption_family s with
  | Module_Lattice => 1
  | Hash_Based => 2
  end.

Definition is_primary_scheme (s : pq_signature_scheme) : bool :=
  scheme_eqb s primary_signature_scheme.

Definition is_fallback_scheme (s : pq_signature_scheme) : bool :=
  scheme_eqb s fallback_signature_scheme.

Definition profile_row (s : pq_signature_scheme) : list nat :=
  [
    scheme_code s;
    standard_code s;
    role_code s;
    assumption_family_code s;
    target_quantum_security_bits s;
    pk_len s;
    sig_len s;
    witness_size_for_scheme s;
    bool_to_nat (fits_consensus_witness_cap s);
    bool_to_nat (implemented_verifier s);
    bool_to_nat (consensus_enabled s);
    bool_to_nat (is_primary_scheme s);
    bool_to_nat (is_fallback_scheme s)
  ].

Definition implemented_scheme_codes : list nat :=
  map scheme_code (filter implemented_verifier all_signature_schemes).

Definition consensus_enabled_scheme_codes : list nat :=
  map scheme_code (filter consensus_enabled all_signature_schemes).

Definition standards_distinct_bool : bool :=
  negb (standard_eqb
    (scheme_standard primary_signature_scheme)
    (scheme_standard fallback_signature_scheme)).

Definition assumptions_distinct_bool : bool :=
  negb (assumption_family_eqb
    (scheme_assumption_family primary_signature_scheme)
    (scheme_assumption_family fallback_signature_scheme)).

Definition all_profiles_fit_cap_bool : bool :=
  forallb fits_consensus_witness_cap all_signature_schemes.

Definition consensus_enabled_exactly_primary_bool : bool :=
  forallb
    (fun s => Bool.eqb (consensus_enabled s) (scheme_eqb s primary_signature_scheme))
    all_signature_schemes.

Definition active_suite_standards_aligned_bool : bool :=
  implemented_verifier primary_signature_scheme
  && standard_eqb (scheme_standard primary_signature_scheme) FIPS_204
  && standard_eqb (scheme_standard fallback_signature_scheme) FIPS_205
  && assumptions_distinct_bool
  && fits_consensus_witness_cap primary_signature_scheme
  && fits_consensus_witness_cap fallback_signature_scheme.

Module PQProfileExtraction.

  Definition extract_profile_rows := map profile_row all_signature_schemes.
  Definition extract_primary_scheme_code := scheme_code primary_signature_scheme.
  Definition extract_fallback_scheme_code := scheme_code fallback_signature_scheme.
  Definition extract_implemented_scheme_codes := implemented_scheme_codes.
  Definition extract_consensus_enabled_scheme_codes := consensus_enabled_scheme_codes.
  Definition extract_standards_distinct := standards_distinct_bool.
  Definition extract_assumptions_distinct := assumptions_distinct_bool.
  Definition extract_all_profiles_fit_cap := all_profiles_fit_cap_bool.
  Definition extract_consensus_enabled_exactly_primary :=
    consensus_enabled_exactly_primary_bool.
  Definition extract_active_suite_standards_aligned :=
    active_suite_standards_aligned_bool.

End PQProfileExtraction.

Extraction Language OCaml.
