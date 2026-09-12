(*
  PQProfile: standards-aligned signature-suite profile invariants.

  This file does not prove cryptographic security of ML-DSA or SLH-DSA.
  Its purpose is narrower and consensus-critical: the executable protocol
  tracks both the deployed FIPS 204 ML-DSA-44 verifier and a reserved FIPS 205
  SLH-DSA-128s fallback profile, while proving that profile metadata cannot be
  confused with consensus activation.
*)

From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.

Inductive pq_signature_scheme : Type :=
| ML_DSA_44
| SLH_DSA_128S.

Inductive pq_standard : Type :=
| FIPS_204
| FIPS_205.

Inductive assumption_family : Type :=
| Module_Lattice
| Hash_Based.

Definition primary_signature_scheme : pq_signature_scheme := ML_DSA_44.
Definition fallback_signature_scheme : pq_signature_scheme := SLH_DSA_128S.

Definition ml_dsa_44_public_key_len : nat := 13 * 100 + 12.
Definition ml_dsa_44_signature_len : nat := 24 * 100 + 20.
Definition slh_dsa_128s_public_key_len : nat := 32.
Definition slh_dsa_128s_signature_len : nat := 78 * 100 + 56.
Definition max_u16 : nat := 655 * 100 + 35.
Definition max_witness_size : nat := 160 * 100.
Definition ml_dsa_44_serialized_witness_size : nat := 37 * 100 + 38.
Definition slh_dsa_128s_serialized_witness_size : nat := 78 * 100 + 92.

Definition scheme_standard (s : pq_signature_scheme) : pq_standard :=
  match s with
  | ML_DSA_44 => FIPS_204
  | SLH_DSA_128S => FIPS_205
  end.

Definition scheme_assumption_family (s : pq_signature_scheme) : assumption_family :=
  match s with
  | ML_DSA_44 => Module_Lattice
  | SLH_DSA_128S => Hash_Based
  end.

Definition pk_len (s : pq_signature_scheme) : nat :=
  match s with
  | ML_DSA_44 => ml_dsa_44_public_key_len
  | SLH_DSA_128S => slh_dsa_128s_public_key_len
  end.

Definition sig_len (s : pq_signature_scheme) : nat :=
  match s with
  | ML_DSA_44 => ml_dsa_44_signature_len
  | SLH_DSA_128S => slh_dsa_128s_signature_len
  end.

Definition target_quantum_security_bits (_ : pq_signature_scheme) : nat := 128.

Definition implemented_verifier (s : pq_signature_scheme) : bool :=
  match s with
  | ML_DSA_44 => true
  | SLH_DSA_128S => false
  end.

Definition compact_size_len (n : nat) : nat :=
  if n <=? 252 then 1
  else if n <=? max_u16 then 3
  else 0.

Definition witness_size_for_scheme (s : pq_signature_scheme) : nat :=
  compact_size_len (pk_len s) + pk_len s
  + compact_size_len (sig_len s) + sig_len s.

Definition fits_consensus_witness_cap (s : pq_signature_scheme) : bool :=
  witness_size_for_scheme s <=? max_witness_size.

Definition consensus_enabled (s : pq_signature_scheme) : bool :=
  implemented_verifier s && fits_consensus_witness_cap s.

Theorem ml_dsa_44_witness_size :
  witness_size_for_scheme ML_DSA_44 = ml_dsa_44_serialized_witness_size.
Proof. reflexivity. Qed.

Theorem slh_dsa_128s_witness_size :
  witness_size_for_scheme SLH_DSA_128S = slh_dsa_128s_serialized_witness_size.
Proof. reflexivity. Qed.

Theorem ml_dsa_44_fits_consensus_witness_cap :
  fits_consensus_witness_cap ML_DSA_44 = true.
Proof. reflexivity. Qed.

Theorem slh_dsa_128s_fits_consensus_witness_cap :
  fits_consensus_witness_cap SLH_DSA_128S = true.
Proof. reflexivity. Qed.

Theorem primary_verifier_implemented :
  implemented_verifier primary_signature_scheme = true.
Proof. reflexivity. Qed.

Theorem fallback_reserved_until_verifier_exists :
  consensus_enabled fallback_signature_scheme = false.
Proof. reflexivity. Qed.

Theorem standards_are_distinct :
  scheme_standard primary_signature_scheme <>
  scheme_standard fallback_signature_scheme.
Proof. discriminate. Qed.

Theorem assumption_families_are_distinct :
  scheme_assumption_family primary_signature_scheme <>
  scheme_assumption_family fallback_signature_scheme.
Proof. discriminate. Qed.

Theorem target_security_is_128_bits :
  forall s, target_quantum_security_bits s = 128.
Proof. intros []; reflexivity. Qed.

Theorem consensus_enabled_implies_implemented_verifier :
  forall s,
    consensus_enabled s = true ->
    implemented_verifier s = true.
Proof.
  intros [] H; simpl in *; try discriminate; reflexivity.
Qed.

Theorem consensus_enabled_implies_witness_cap :
  forall s,
    consensus_enabled s = true ->
    fits_consensus_witness_cap s = true.
Proof.
  intros [] H; simpl in *; try discriminate; reflexivity.
Qed.

Theorem primary_scheme_is_only_consensus_enabled_scheme :
  forall s,
    consensus_enabled s = true ->
    s = primary_signature_scheme.
Proof.
  intros [] H; simpl in *; try discriminate; reflexivity.
Qed.

Theorem tracked_profiles_fit_current_consensus_cap :
  forall s, witness_size_for_scheme s <= max_witness_size.
Proof.
  intros []; cbv; lia.
Qed.
