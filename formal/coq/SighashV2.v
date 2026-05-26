(** * SighashV2: Mechanized Sighash v2 Model for PO-4
 *
 * Copyright (c) 2026 Mayckon Giovani. MIT License.
 *
 * This module formalizes the Sighash v2 construction and proves the three
 * properties required for PO-4 (Sighash Commitment):
 *   1. Injectivity: different consensus-significant fields → different sighashes
 *   2. Cross-input separation: sighash commits to input index
 *   3. Field coverage: all consensus-critical fields committed
 *
 * The sighash structure follows BIP 341 with PQ-specific domain separation:
 *   - Tagged hashes with "PQWitness/" prefix
 *   - Epoch byte 0x02 for version separation
 *   - Explicit input index commitment
 *)

From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import PeanoNat.
From Coq Require Import Lia.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import ProofIrrelevance.
From Coq Require Import Arith.

Import ListNotations.

(** Power of 2 constants defined via computation to avoid large literal parsing *)
Definition pow2_8 : nat := 256.
Definition pow2_16 : nat := 256 * 256.
Definition pow2_24 : nat := 256 * 256 * 256.
Definition pow2_32 : nat := 256 * 256 * 256 * 256.
Definition pow2_64 : nat := pow2_32 * pow2_32.

(* ================================================================= *)
(* Part I: Cryptographic Primitives (Axiomatized)                  *)
(* ================================================================= *)

(** SHA-256 hash function - axiomatized as a collision-resistant hash *)
Parameter SHA256 : list nat -> list nat.

(** Hash output length is always 32 bytes *)
Axiom sha256_length : forall data, length (SHA256 data) = 32.

(** Collision resistance: if SHA256(x) = SHA256(y), then x = y
    (except with negligible probability - this is an axiom) *)
Axiom sha256_collision_resistance :
  forall x y, SHA256 x = SHA256 y -> x = y.

(** Tagged hash construction: SHA256(SHA256(tag) || SHA256(tag) || data)
    Tags are passed as lists of bytes (nat) to avoid string conversion issues *)
Definition tagged_hash (tag : list nat) (data : list nat) : list nat :=
  let tag_hash := SHA256 tag in
  SHA256 (tag_hash ++ tag_hash ++ data).

(** Domain separation tags for sighash v2 - as byte sequences *)
Definition TAG_SIGHASH : list nat :=
  [80; 81; 87; 105; 116; 110; 101; 115; 115; 47; 115; 105; 103; 104; 97; 115; 104].

Definition TAG_OUTPOINTS : list nat :=
  [80; 81; 87; 105; 116; 110; 101; 115; 115; 47; 111; 117; 116; 112; 111; 105; 110; 116; 115].

Definition TAG_OUTPUTS : list nat :=
  [80; 81; 87; 105; 116; 110; 101; 115; 115; 47; 111; 117; 116; 112; 117; 116; 115].

(* ================================================================= *)
(* Part II: Transaction Structure                                    *)
(* ================================================================= *)

(** An outpoint is a 32-byte txid + 4-byte vout *)
Record OutPoint : Type := mkOutPoint {
  op_txid : list nat;      (* 32 bytes *)
  op_vout : nat             (* 4 bytes as little-endian *)
}.

(** A transaction output *)
Record TxOutput : Type := mkTxOutput {
  txo_script_version : nat;  (* 1 byte *)
  txo_commitment : list nat; (* 32 bytes *)
  txo_value : nat            (* 8 bytes as little-endian *)
}.

(** A transaction input references an outpoint *)
Record TxInput : Type := mkTxInput {
  txi_outpoint : OutPoint;
  txi_witness : list nat      (* Not used in sighash computation *)
}.

(** Spent output context (the UTXO being spent) *)
Record SpentOutput : Type := mkSpentOutput {
  so_script_version : nat;   (* 1 byte *)
  so_commitment : list nat;  (* 32 bytes *)
  so_value : nat             (* 8 bytes *)
}.

(** A complete transaction *)
Record Transaction : Type := mkTransaction {
  tx_version : nat;           (* 4 bytes *)
  tx_inputs : list TxInput;
  tx_outputs : list TxOutput;
  tx_locktime : nat           (* 4 bytes *)
}.

Definition tx_input_outpoints (tx : Transaction) : list OutPoint :=
  map (fun inp => inp.(txi_outpoint)) tx.(tx_inputs).

Definition byte (b : nat) : Prop := b <= 255.

Definition bytes (bs : list nat) : Prop := Forall byte bs.

Definition wf_outpoint (op : OutPoint) : Prop :=
  length op.(op_txid) = 32 /\
  bytes op.(op_txid) /\
  op.(op_vout) < pow2_32.

Definition wf_tx_input (txi : TxInput) : Prop :=
  wf_outpoint txi.(txi_outpoint).

Definition wf_tx_output (txo : TxOutput) : Prop :=
  byte txo.(txo_script_version) /\
  length txo.(txo_commitment) = 32 /\
  bytes txo.(txo_commitment) /\
  txo.(txo_value) < pow2_64.

Definition wf_spent_output (so : SpentOutput) : Prop :=
  byte so.(so_script_version) /\
  length so.(so_commitment) = 32 /\
  bytes so.(so_commitment) /\
  so.(so_value) < pow2_64.

Definition wf_transaction (tx : Transaction) : Prop :=
  tx.(tx_version) < pow2_32 /\
  Forall wf_tx_input tx.(tx_inputs) /\
  Forall wf_tx_output tx.(tx_outputs) /\
  tx.(tx_locktime) < pow2_32.

(* ================================================================= *)
(* Part III: Sighash v2 Computation                                  *)
(* ================================================================= *)

(** Convert nat to 4 little-endian bytes using pow2 definitions *)
Definition nat_to_le4 (n : nat) : list nat :=
  [n mod pow2_8; (n / pow2_8) mod pow2_8; (n / pow2_16) mod pow2_8; (n / pow2_24) mod pow2_8].

(** Convert nat to 8 little-endian bytes using pow2 definitions *)
Definition nat_to_le8 (n : nat) : list nat :=
  [n mod pow2_8;
   (n / pow2_8) mod pow2_8;
   (n / pow2_16) mod pow2_8;
   (n / pow2_24) mod pow2_8;
   (n / pow2_32) mod pow2_8;
   (n / pow2_32 / pow2_8) mod pow2_8;
   (n / pow2_32 / pow2_16) mod pow2_8;
   (n / pow2_32 / pow2_24) mod pow2_8].

(** Serialize an outpoint: txid || vout_le *)
Definition serialize_outpoint (op : OutPoint) : list nat :=
  op.(op_txid) ++ nat_to_le4 op.(op_vout).

(** Serialize an output: script_version || commitment || value_le *)
Definition serialize_output (txo : TxOutput) : list nat :=
  [txo.(txo_script_version)] ++ txo.(txo_commitment) ++ nat_to_le8 txo.(txo_value).

(** Serialize a spent output: script_version || commitment || value_le *)
Definition serialize_spent_output (so : SpentOutput) : list nat :=
  [so.(so_script_version)] ++ so.(so_commitment) ++ nat_to_le8 so.(so_value).

(** Compute hash of all input outpoints *)
Definition hash_outpoints (inputs : list TxInput) : list nat :=
  let data := concat (map (fun inp => serialize_outpoint inp.(txi_outpoint)) inputs) in
  tagged_hash TAG_OUTPOINTS data.

(** Compute hash of all outputs *)
Definition hash_outputs (outputs : list TxOutput) : list nat :=
  let data := concat (map serialize_output outputs) in
  tagged_hash TAG_OUTPUTS data.

(** Epoch byte for PQ domain separation from v0/v1 *)
Definition PQ_EPOCH_BYTE : nat := 2.

(** Spend type: 0x00 for key-path spend *)
Definition SPEND_TYPE_KEY_PATH : nat := 0.

(** Final sighash preimage assembly with supplied 32-byte sub-hashes.
    This separates deterministic transcript serialization from the SHA-256
    assumption, and is the function extracted for Rust transcript refinement. *)
Definition sighash_preimage_from_hashes
  (tx : Transaction)
  (input_index : nat)
  (spent : SpentOutput)
  (h_outpoints h_outputs : list nat) : list nat :=
  [PQ_EPOCH_BYTE] ++
  nat_to_le4 tx.(tx_version) ++
  h_outpoints ++
  h_outputs ++
  [SPEND_TYPE_KEY_PATH] ++
  serialize_spent_output spent ++
  nat_to_le4 input_index ++
  nat_to_le4 tx.(tx_locktime).

(** Final sighash preimage before the outer tagged hash. *)
Definition sighash_preimage (tx : Transaction) (input_index : nat) (spent : SpentOutput) : list nat :=
  let h_outpoints := hash_outpoints tx.(tx_inputs) in
  let h_outputs := hash_outputs tx.(tx_outputs) in
  sighash_preimage_from_hashes tx input_index spent h_outpoints h_outputs.

Theorem sighash_preimage_from_hashes_agrees : forall tx input_index spent,
  sighash_preimage tx input_index spent =
  sighash_preimage_from_hashes
    tx input_index spent
    (hash_outpoints tx.(tx_inputs))
    (hash_outputs tx.(tx_outputs)).
Proof.
  reflexivity.
Qed.

(** Compute sighash v2 for a specific input *)
Definition sighash_v2 (tx : Transaction) (input_index : nat) (spent : SpentOutput) : list nat :=
  tagged_hash TAG_SIGHASH (sighash_preimage tx input_index spent).

(* ================================================================= *)
(* Part IV: Helper Lemmas                                            *)
(* ================================================================= *)

(** Helper: List concatenation is injective on the right *)
Lemma app_inj_tail : forall (A : Type) (l1 l2 r1 r2 : list A),
  length l1 = length l2 -> l1 ++ r1 = l2 ++ r2 -> l1 = l2 /\ r1 = r2.
Proof.
  intros A l1 l2 r1 r2 Hlen Heq.
  generalize dependent l2.
  generalize dependent r1.
  generalize dependent r2.
  induction l1 as [|a l1' IH]; intros r2 r1 l2 Hlen Heq.
  - simpl in Hlen. destruct l2 as [|b l2'].
    + simpl in Heq. split; [reflexivity | assumption].
    + simpl in Hlen. discriminate Hlen.
  - destruct l2 as [|b l2'].
    + simpl in Hlen. discriminate Hlen.
    + simpl in Hlen. injection Hlen as Hlen'.
      simpl in Heq. injection Heq as Hhead Htail.
      apply IH with (r1 := r1) (r2 := r2) in Hlen'.
      * destruct Hlen' as [Hl Hr].
        split.
        -- rewrite Hl. rewrite Hhead. reflexivity.
        -- assumption.
      * assumption.
Qed.

(** Helper: Equality inversion for fixed-width 4-byte lists *)
Lemma list4_eq_inv : forall (A : Type) (a0 a1 a2 a3 b0 b1 b2 b3 : A),
  [a0; a1; a2; a3] = [b0; b1; b2; b3] ->
  a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3.
Proof.
  intros A a0 a1 a2 a3 b0 b1 b2 b3 H.
  repeat split.
  - exact (f_equal (fun xs => nth 0 xs a0) H).
  - exact (f_equal (fun xs => nth 1 xs a0) H).
  - exact (f_equal (fun xs => nth 2 xs a0) H).
  - exact (f_equal (fun xs => nth 3 xs a0) H).
Qed.

(** Helper: Equality inversion for fixed-width 8-byte lists *)
Lemma list8_eq_inv : forall (A : Type) (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : A),
  [a0; a1; a2; a3; a4; a5; a6; a7] = [b0; b1; b2; b3; b4; b5; b6; b7] ->
  a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3 /\
  a4 = b4 /\ a5 = b5 /\ a6 = b6 /\ a7 = b7.
Proof.
  intros A a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 H.
  repeat split.
  - exact (f_equal (fun xs => nth 0 xs a0) H).
  - exact (f_equal (fun xs => nth 1 xs a0) H).
  - exact (f_equal (fun xs => nth 2 xs a0) H).
  - exact (f_equal (fun xs => nth 3 xs a0) H).
  - exact (f_equal (fun xs => nth 4 xs a0) H).
  - exact (f_equal (fun xs => nth 5 xs a0) H).
  - exact (f_equal (fun xs => nth 6 xs a0) H).
  - exact (f_equal (fun xs => nth 7 xs a0) H).
Qed.

(** Helper: Equal tagged hashes imply equal preimages *)
Lemma tagged_hash_injective : forall tag d1 d2,
  tagged_hash tag d1 = tagged_hash tag d2 -> d1 = d2.
Proof.
  intros tag d1 d2 H.
  unfold tagged_hash in H.
  apply sha256_collision_resistance in H.
  (* Now H: SHA256 tag ++ SHA256 tag ++ d1 = SHA256 tag ++ SHA256 tag ++ d2 *)
  assert (length (SHA256 tag) = length (SHA256 tag)) as Hlen by reflexivity.
  apply (app_inj_tail nat _ _ _ _ Hlen) in H.
  destruct H as [_ H2].
  apply (app_inj_tail nat _ _ _ _ Hlen) in H2.
  destruct H2 as [_ H3].
  assumption.
Qed.

(** Helper: Tagged hashes have SHA-256 output length *)
Lemma tagged_hash_length : forall tag data,
  length (tagged_hash tag data) = 32.
Proof.
  intros tag data.
  unfold tagged_hash.
  apply sha256_length.
Qed.

(** Helper: Reconstruct number from 4 little-endian bytes
    Using nested multiplication to avoid explicit large constants *)
Definition reconstruct_le4 (b0 b1 b2 b3 : nat) : nat :=
  b0 + 256 * (b1 + 256 * (b2 + 256 * b3)).

(** Helper: Div_mod_256 - core property for little-endian reconstruction
    Matches Nat.div_mod: n = 256 * (n / 256) + n mod 256 *)
Lemma div_mod_256 : forall n,
  n = 256 * (n / 256) + (n mod 256).
Proof.
  intros n.
  exact (Nat.div_mod_eq n 256).
Qed.

(** Helper: Reconstruct 4-byte little-endian value without expanding constants *)
Definition reconstruct_le4_explicit (n : nat) : nat :=
  let b0 := n mod pow2_8 in
  let b1 := (n / pow2_8) mod pow2_8 in
  let b2 := (n / pow2_16) mod pow2_8 in
  let b3 := (n / pow2_24) mod pow2_8 in
  b0 + pow2_8 * b1 + pow2_16 * b2 + pow2_24 * b3.

(** Helper: nat_to_le4 reconstruction property
    This lemma states that reconstructing a 4-byte little-endian value gives back n mod 2^32.

    Mathematical justification:
    By the division theorem: n = 256*(n/256) + n mod 256
    Expanding recursively: n = b0 + 256*b1 + 256^2*b2 + 256^3*b3 + 256^4*q
    where b0 = n mod 256, b1 = (n/256) mod 256, etc.
    Therefore: n mod 2^32 = b0 + 256*b1 + 256^2*b2 + 256^3*b3
    which is exactly what reconstruct_le4 computes.

    This proof avoids large literal expansion by decomposing the modulus as
    repeated base-256 products. *)
Lemma nat_to_le4_reconstruct : forall n,
  reconstruct_le4 (n mod pow2_8) ((n / pow2_8) mod pow2_8) ((n / pow2_16) mod pow2_8) ((n / pow2_24) mod pow2_8) = n mod pow2_32.
Proof.
  intros n.
  unfold reconstruct_le4.
  replace pow2_32 with (pow2_8 * pow2_24)
    by (unfold pow2_32, pow2_24, pow2_8; lia).
  rewrite (Nat.Div0.mod_mul_r n pow2_8 pow2_24).
  replace pow2_24 with (pow2_8 * pow2_16)
    by (unfold pow2_24, pow2_16, pow2_8; lia).
  rewrite (Nat.Div0.mod_mul_r (n / pow2_8) pow2_8 pow2_16).
  replace ((n / pow2_8) / pow2_8) with (n / pow2_16).
  2:{ unfold pow2_16, pow2_8. rewrite Nat.Div0.div_div. reflexivity. }
  replace pow2_16 with (pow2_8 * pow2_8)
    by (unfold pow2_16, pow2_8; lia).
  rewrite (Nat.Div0.mod_mul_r (n / (pow2_8 * pow2_8)) pow2_8 pow2_8).
  replace ((n / (pow2_8 * pow2_8)) / pow2_8) with (n / pow2_24).
  2:{ unfold pow2_24, pow2_8. rewrite <- Nat.Div0.div_div. reflexivity. }
  unfold pow2_24, pow2_8.
  replace (256 * (256 * 256)) with (256 * 256 * 256) by lia.
  reflexivity.
Qed.

(** Lemma: nat_to_le4 is injective for values less than 2^32
    This is the KEY PROPERTY for PO-4: different 4-byte values produce different encodings.

    Mathematical justification:
    The 4-byte little-endian encoding maps n to [b0, b1, b2, b3] where
    bi = floor(n/256^i) mod 256. This is the standard base-256 representation.
    For n < 2^32, this representation is UNIQUE (bijection between [0,2^32) and bytes).
    Therefore, if encodings are equal, the original values must be equal.

    The proof reconstructs both values from their equal byte components and
    uses the explicit u32 bounds to collapse modulo 2^32. *)
Lemma nat_to_le4_injective : forall n m,
  n < pow2_32 -> m < pow2_32 ->
  nat_to_le4 n = nat_to_le4 m -> n = m.
Proof.
  intros n m Hn Hm Heq.
  assert (Hrn : n = reconstruct_le4
    (n mod pow2_8)
    ((n / pow2_8) mod pow2_8)
    ((n / pow2_16) mod pow2_8)
    ((n / pow2_24) mod pow2_8)).
  { rewrite nat_to_le4_reconstruct. symmetry. apply Nat.mod_small. exact Hn. }
  assert (Hrm : m = reconstruct_le4
    (m mod pow2_8)
    ((m / pow2_8) mod pow2_8)
    ((m / pow2_16) mod pow2_8)
    ((m / pow2_24) mod pow2_8)).
  { rewrite nat_to_le4_reconstruct. symmetry. apply Nat.mod_small. exact Hm. }
  unfold nat_to_le4 in Heq.
  apply list4_eq_inv in Heq.
  destruct Heq as [Hb0 [Hb1 [Hb2 Hb3]]].
  rewrite Hrn, Hrm.
  unfold reconstruct_le4.
  rewrite Hb0, Hb1, Hb2, Hb3.
  reflexivity.
Qed.

(** Helper: Reconstruct number from 8 little-endian bytes
    Using nested multiplication (two levels of reconstruct_le4) *)
Definition reconstruct_le8 (b0 b1 b2 b3 b4 b5 b6 b7 : nat) : nat :=
  let low := reconstruct_le4 b0 b1 b2 b3 in
  let high := reconstruct_le4 b4 b5 b6 b7 in
  low + pow2_32 * high.

(** Helper: nat_to_le8 reconstruction property
    This lemma states that reconstructing an 8-byte little-endian value gives back n mod 2^64.

    Mathematical justification:
    Similar to nat_to_le4_reconstruct but with 8 levels of base-256 decomposition.
    n mod 2^64 = b0 + 256*b1 + 256^2*b2 + ... + 256^7*b7
    where bi = floor(n/256^i) mod 256.
    This is the standard positional numeral system expansion.

    The proof decomposes the 8-byte value into low/high u32 halves and reuses
    nat_to_le4_reconstruct. *)
Lemma nat_to_le8_reconstruct : forall n,
  reconstruct_le8 (n mod pow2_8) ((n / pow2_8) mod pow2_8) ((n / pow2_16) mod pow2_8) ((n / pow2_24) mod pow2_8)
                 ((n / pow2_32) mod pow2_8) ((n / pow2_32 / pow2_8) mod pow2_8) ((n / pow2_32 / pow2_16) mod pow2_8) ((n / pow2_32 / pow2_24) mod pow2_8) = n mod pow2_64.
Proof.
  intros n.
  unfold reconstruct_le8.
  rewrite nat_to_le4_reconstruct.
  rewrite nat_to_le4_reconstruct.
  unfold pow2_64.
  rewrite (Nat.Div0.mod_mul_r n pow2_32 pow2_32).
  reflexivity.
Qed.


(** Lemma: nat_to_le8 is injective for values less than 2^64
    This property ensures that 8-byte little-endian encodings are unique.

    Mathematical justification:
    Similar to nat_to_le4_injective. The 8-byte encoding is bijective on [0, 2^64).
    Equal encodings imply equal bytes, which by base-256 expansion implies equal values.
    Therefore, nat_to_le8 is injective for bounded inputs.

    The proof reconstructs both values from equal byte components and uses the
    explicit u64 bounds to collapse modulo 2^64. *)
Lemma nat_to_le8_injective : forall n m,
  n < pow2_64 -> m < pow2_64 ->
  nat_to_le8 n = nat_to_le8 m -> n = m.
Proof.
  intros n m Hn Hm Heq.
  assert (Hrn : n = reconstruct_le8
    (n mod pow2_8)
    ((n / pow2_8) mod pow2_8)
    ((n / pow2_16) mod pow2_8)
    ((n / pow2_24) mod pow2_8)
    ((n / pow2_32) mod pow2_8)
    ((n / pow2_32 / pow2_8) mod pow2_8)
    ((n / pow2_32 / pow2_16) mod pow2_8)
    ((n / pow2_32 / pow2_24) mod pow2_8)).
  { rewrite nat_to_le8_reconstruct. symmetry. apply Nat.mod_small. exact Hn. }
  assert (Hrm : m = reconstruct_le8
    (m mod pow2_8)
    ((m / pow2_8) mod pow2_8)
    ((m / pow2_16) mod pow2_8)
    ((m / pow2_24) mod pow2_8)
    ((m / pow2_32) mod pow2_8)
    ((m / pow2_32 / pow2_8) mod pow2_8)
    ((m / pow2_32 / pow2_16) mod pow2_8)
    ((m / pow2_32 / pow2_24) mod pow2_8)).
  { rewrite nat_to_le8_reconstruct. symmetry. apply Nat.mod_small. exact Hm. }
  unfold nat_to_le8 in Heq.
  apply list8_eq_inv in Heq.
  destruct Heq as [Hb0 [Hb1 [Hb2 [Hb3 [Hb4 [Hb5 [Hb6 Hb7]]]]]]].
  rewrite Hrn, Hrm.
  unfold reconstruct_le8, reconstruct_le4.
  rewrite Hb0, Hb1, Hb2, Hb3, Hb4, Hb5, Hb6, Hb7.
  reflexivity.
Qed.

(** Helper: Length of nat_to_le4 is always 4 *)
Lemma nat_to_le4_length : forall n, length (nat_to_le4 n) = 4.
Proof.
  intros n. unfold nat_to_le4. reflexivity.
Qed.

(** Helper: Length of nat_to_le8 is always 8 *)
Lemma nat_to_le8_length : forall n, length (nat_to_le8 n) = 8.
Proof.
  intros n. unfold nat_to_le8. reflexivity.
Qed.

(** Helper: Last 4 elements of a concatenated list
    If two concatenations have equal suffixes (the last 4 bytes from nat_to_le4),
    the prefixes have equal length, and both encoded values fit in u32, then
    the values are equal.

    Mathematical justification: nat_to_le4 produces a unique 4-byte encoding
    for each value in [0, 2^32). Equal suffixes imply equal values. *)
Lemma app_last_4_eq : forall (l1 l2 : list nat) (vout1 vout2 : nat),
  vout1 < pow2_32 ->
  vout2 < pow2_32 ->
  l1 ++ nat_to_le4 vout1 = l2 ++ nat_to_le4 vout2 ->
  length l1 = length l2 ->
  vout1 = vout2.
Proof.
  intros l1 l2 vout1 vout2 Hvout1 Hvout2 Heq Hlen.
  pose proof (app_inj_tail nat l1 l2
    (nat_to_le4 vout1) (nat_to_le4 vout2) Hlen Heq) as [_ Hsuffix].
  eapply nat_to_le4_injective; eauto.
Qed.

(** Lemma: serialize_outpoint is injective for well-formed outpoints
    If two fixed-width outpoints serialize to the same bytes, they are equal.

    Mathematical justification:
    Serialization produces: txid || nat_to_le4(vout)
    Equal serializations imply:
    1. txid1 = txid2 (prefixes of equal-length concatenations)
    2. nat_to_le4(vout1) = nat_to_le4(vout2) (suffixes)
    By nat_to_le4_injective and vout < 2^32 (Bitcoin constraint), vout1 = vout2.
    Therefore op1 = op2. *)
Lemma serialize_outpoint_injective : forall op1 op2,
  wf_outpoint op1 ->
  wf_outpoint op2 ->
  serialize_outpoint op1 = serialize_outpoint op2 -> op1 = op2.
Proof.
  intros [txid1 vout1] [txid2 vout2] Hwf1 Hwf2 Hser.
  unfold wf_outpoint in *.
  simpl in *.
  destruct Hwf1 as [Hlen1 [_ Hvout1]].
  destruct Hwf2 as [Hlen2 [_ Hvout2]].
  unfold serialize_outpoint in Hser.
  simpl in Hser.
  assert (Hlen : length txid1 = length txid2) by lia.
  pose proof (app_inj_tail nat txid1 txid2
    (nat_to_le4 vout1) (nat_to_le4 vout2) Hlen Hser) as [Htxid Hsuffix].
  assert (Hvout : vout1 = vout2).
  { eapply nat_to_le4_injective; eauto. }
  subst vout2.
  rewrite Htxid.
  reflexivity.
Qed.

(** Serialized outpoints have fixed 36-byte width under wf_outpoint. *)
Lemma serialize_outpoint_length : forall op,
  wf_outpoint op ->
  length (serialize_outpoint op) = 36.
Proof.
  intros [txid vout] Hwf.
  unfold wf_outpoint in Hwf.
  simpl in *.
  destruct Hwf as [Hlen [_ _]].
  unfold serialize_outpoint.
  simpl.
  rewrite app_length.
  rewrite Hlen.
  rewrite nat_to_le4_length.
  reflexivity.
Qed.

(** Serialized transaction outputs have fixed 41-byte width under wf_tx_output. *)
Lemma serialize_output_length : forall txo,
  wf_tx_output txo ->
  length (serialize_output txo) = 41.
Proof.
  intros [sv commitment value] Hwf.
  unfold wf_tx_output in Hwf.
  simpl in *.
  destruct Hwf as [_ [Hlen [_ _]]].
  unfold serialize_output.
  simpl.
  repeat rewrite app_length.
  simpl.
  rewrite Hlen.
  lia.
Qed.

(** Serialized spent outputs have fixed 41-byte width under wf_spent_output. *)
Lemma serialize_spent_output_length : forall so,
  wf_spent_output so ->
  length (serialize_spent_output so) = 41.
Proof.
  intros [sv commitment value] Hwf.
  unfold wf_spent_output in Hwf.
  simpl in *.
  destruct Hwf as [_ [Hlen [_ _]]].
  unfold serialize_spent_output.
  simpl.
  repeat rewrite app_length.
  simpl.
  rewrite Hlen.
  lia.
Qed.

(** Transaction output serialization is injective for well-formed outputs. *)
Lemma serialize_output_injective : forall txo1 txo2,
  wf_tx_output txo1 ->
  wf_tx_output txo2 ->
  serialize_output txo1 = serialize_output txo2 -> txo1 = txo2.
Proof.
  intros [sv1 commitment1 value1] [sv2 commitment2 value2] Hwf1 Hwf2 Hser.
  unfold wf_tx_output in *.
  simpl in *.
  destruct Hwf1 as [_ [Hlen1 [_ Hvalue1]]].
  destruct Hwf2 as [_ [Hlen2 [_ Hvalue2]]].
  unfold serialize_output in Hser.
  simpl in Hser.
  injection Hser as Hsv Hrest.
  assert (Hlen : length commitment1 = length commitment2) by lia.
  pose proof (app_inj_tail nat commitment1 commitment2
    (nat_to_le8 value1) (nat_to_le8 value2) Hlen Hrest) as [Hcommitment Hsuffix].
  assert (Hvalue : value1 = value2).
  { eapply nat_to_le8_injective; eauto. }
  subst value2.
  rewrite Hsv.
  rewrite Hcommitment.
  reflexivity.
Qed.

(** Spent output serialization is injective for well-formed spent outputs. *)
Lemma serialize_spent_output_injective : forall so1 so2,
  wf_spent_output so1 ->
  wf_spent_output so2 ->
  serialize_spent_output so1 = serialize_spent_output so2 -> so1 = so2.
Proof.
  intros [sv1 commitment1 value1] [sv2 commitment2 value2] Hwf1 Hwf2 Hser.
  unfold wf_spent_output in *.
  simpl in *.
  destruct Hwf1 as [_ [Hlen1 [_ Hvalue1]]].
  destruct Hwf2 as [_ [Hlen2 [_ Hvalue2]]].
  unfold serialize_spent_output in Hser.
  simpl in Hser.
  injection Hser as Hsv Hrest.
  assert (Hlen : length commitment1 = length commitment2) by lia.
  pose proof (app_inj_tail nat commitment1 commitment2
    (nat_to_le8 value1) (nat_to_le8 value2) Hlen Hrest) as [Hcommitment Hsuffix].
  assert (Hvalue : value1 = value2).
  { eapply nat_to_le8_injective; eauto. }
  subst value2.
  rewrite Hsv.
  rewrite Hcommitment.
  reflexivity.
Qed.

(** Concatenated input-outpoint serialization is injective over well-formed inputs. *)
Lemma concat_input_outpoints_injective : forall inputs1 inputs2,
  Forall wf_tx_input inputs1 ->
  Forall wf_tx_input inputs2 ->
  concat (map (fun inp => serialize_outpoint inp.(txi_outpoint)) inputs1) =
  concat (map (fun inp => serialize_outpoint inp.(txi_outpoint)) inputs2) ->
  map (fun inp => inp.(txi_outpoint)) inputs1 =
  map (fun inp => inp.(txi_outpoint)) inputs2.
Proof.
  induction inputs1 as [|input1 inputs1 IH]; intros inputs2 Hwf1 Hwf2 Hser.
  - destruct inputs2 as [|input2 inputs2].
    + reflexivity.
    + inversion Hwf2 as [|? ? Hinput2 _]; subst.
      simpl in Hser.
      pose proof (serialize_outpoint_length input2.(txi_outpoint) Hinput2) as Hlen.
      assert (length (serialize_outpoint input2.(txi_outpoint) ++
        concat (map (fun inp => serialize_outpoint inp.(txi_outpoint)) inputs2)) = 0) as Hzero.
      { rewrite <- Hser. reflexivity. }
      rewrite app_length in Hzero.
      lia.
  - inversion Hwf1 as [|? ? Hinput1 Hinputs1]; subst.
    destruct inputs2 as [|input2 inputs2].
    + simpl in Hser.
      pose proof (serialize_outpoint_length input1.(txi_outpoint) Hinput1) as Hlen.
      assert (length (serialize_outpoint input1.(txi_outpoint) ++
        concat (map (fun inp => serialize_outpoint inp.(txi_outpoint)) inputs1)) = 0) as Hzero.
      { rewrite Hser. reflexivity. }
      rewrite app_length in Hzero.
      lia.
    + inversion Hwf2 as [|? ? Hinput2 Hinputs2]; subst.
      simpl in Hser.
      pose proof (serialize_outpoint_length input1.(txi_outpoint) Hinput1) as Hlen1.
      pose proof (serialize_outpoint_length input2.(txi_outpoint) Hinput2) as Hlen2.
      assert (Hlen : length (serialize_outpoint input1.(txi_outpoint)) =
                     length (serialize_outpoint input2.(txi_outpoint))) by lia.
      pose proof (app_inj_tail nat
        (serialize_outpoint input1.(txi_outpoint))
        (serialize_outpoint input2.(txi_outpoint))
        (concat (map (fun inp => serialize_outpoint inp.(txi_outpoint)) inputs1))
        (concat (map (fun inp => serialize_outpoint inp.(txi_outpoint)) inputs2))
        Hlen Hser) as [Hhead Htail].
      assert (Houtpoint : input1.(txi_outpoint) = input2.(txi_outpoint)).
      { eapply serialize_outpoint_injective; eauto. }
      simpl.
      rewrite Houtpoint.
      f_equal.
      apply IH; assumption.
Qed.

(** Concatenated output serialization is injective over well-formed outputs. *)
Lemma concat_outputs_injective : forall outputs1 outputs2,
  Forall wf_tx_output outputs1 ->
  Forall wf_tx_output outputs2 ->
  concat (map serialize_output outputs1) =
  concat (map serialize_output outputs2) ->
  outputs1 = outputs2.
Proof.
  induction outputs1 as [|output1 outputs1 IH]; intros outputs2 Hwf1 Hwf2 Hser.
  - destruct outputs2 as [|output2 outputs2].
    + reflexivity.
    + inversion Hwf2 as [|? ? Houtput2 _]; subst.
      simpl in Hser.
      discriminate Hser.
  - inversion Hwf1 as [|? ? Houtput1 Houtputs1]; subst.
    destruct outputs2 as [|output2 outputs2].
    + simpl in Hser.
      discriminate Hser.
    + inversion Hwf2 as [|? ? Houtput2 Houtputs2]; subst.
      simpl in Hser.
      pose proof (serialize_output_length output1 Houtput1) as Hlen1.
      pose proof (serialize_output_length output2 Houtput2) as Hlen2.
      assert (Hlen : length (serialize_output output1) =
                     length (serialize_output output2)) by lia.
      pose proof (app_inj_tail nat
        (serialize_output output1)
        (serialize_output output2)
        (concat (map serialize_output outputs1))
        (concat (map serialize_output outputs2))
        Hlen Hser) as [Hhead Htail].
      assert (Houtput : output1 = output2).
      { eapply serialize_output_injective; eauto. }
      subst output2.
      f_equal.
      apply IH; assumption.
Qed.

(** The input-outpoints sub-hash is injective under SHA-256 collision resistance. *)
Lemma hash_outpoints_injective : forall inputs1 inputs2,
  Forall wf_tx_input inputs1 ->
  Forall wf_tx_input inputs2 ->
  hash_outpoints inputs1 = hash_outpoints inputs2 ->
  map (fun inp => inp.(txi_outpoint)) inputs1 =
  map (fun inp => inp.(txi_outpoint)) inputs2.
Proof.
  intros inputs1 inputs2 Hwf1 Hwf2 Hhash.
  unfold hash_outpoints in Hhash.
  apply tagged_hash_injective in Hhash.
  eapply concat_input_outpoints_injective; eauto.
Qed.

(** The outputs sub-hash is injective under SHA-256 collision resistance. *)
Lemma hash_outputs_injective : forall outputs1 outputs2,
  Forall wf_tx_output outputs1 ->
  Forall wf_tx_output outputs2 ->
  hash_outputs outputs1 = hash_outputs outputs2 ->
  outputs1 = outputs2.
Proof.
  intros outputs1 outputs2 Hwf1 Hwf2 Hhash.
  unfold hash_outputs in Hhash.
  apply tagged_hash_injective in Hhash.
  eapply concat_outputs_injective; eauto.
Qed.

(** Sub-hashes have fixed SHA-256 output width. *)
Lemma hash_outpoints_length : forall inputs,
  length (hash_outpoints inputs) = 32.
Proof.
  intros inputs.
  unfold hash_outpoints.
  apply tagged_hash_length.
Qed.

Lemma hash_outputs_length : forall outputs,
  length (hash_outputs outputs) = 32.
Proof.
  intros outputs.
  unfold hash_outputs.
  apply tagged_hash_length.
Qed.

(* ================================================================= *)
(* Part V: PO-4 Properties - Theorems                              *)
(* ================================================================= *)

(** ** Property 1: Injectivity *)
Theorem sighash_v2_injective : forall tx1 tx2 i1 i2 s1 s2,
  wf_transaction tx1 ->
  wf_transaction tx2 ->
  wf_spent_output s1 ->
  wf_spent_output s2 ->
  i1 < pow2_32 ->
  i2 < pow2_32 ->
  sighash_v2 tx1 i1 s1 = sighash_v2 tx2 i2 s2 ->
  tx1.(tx_version) = tx2.(tx_version) /\
  tx_input_outpoints tx1 = tx_input_outpoints tx2 /\
  tx1.(tx_outputs) = tx2.(tx_outputs) /\
  tx1.(tx_locktime) = tx2.(tx_locktime) /\
  i1 = i2 /\
  s1.(so_script_version) = s2.(so_script_version) /\
  s1.(so_commitment) = s2.(so_commitment) /\
  s1.(so_value) = s2.(so_value).
Proof.
  intros tx1 tx2 i1 i2 s1 s2 Htx1 Htx2 Hs1 Hs2 Hi1 Hi2 Heq.
  unfold sighash_v2 in Heq.
  apply tagged_hash_injective in Heq.
  unfold sighash_preimage in Heq.
  destruct Htx1 as [Hversion1 [Hinputs1 [Houtputs1 Hlocktime1]]].
  destruct Htx2 as [Hversion2 [Hinputs2 [Houtputs2 Hlocktime2]]].

  pose proof (app_inj_tail nat [PQ_EPOCH_BYTE] [PQ_EPOCH_BYTE]
    (nat_to_le4 tx1.(tx_version) ++ hash_outpoints tx1.(tx_inputs) ++
     hash_outputs tx1.(tx_outputs) ++ [SPEND_TYPE_KEY_PATH] ++
     serialize_spent_output s1 ++ nat_to_le4 i1 ++ nat_to_le4 tx1.(tx_locktime))
    (nat_to_le4 tx2.(tx_version) ++ hash_outpoints tx2.(tx_inputs) ++
     hash_outputs tx2.(tx_outputs) ++ [SPEND_TYPE_KEY_PATH] ++
     serialize_spent_output s2 ++ nat_to_le4 i2 ++ nat_to_le4 tx2.(tx_locktime))
    eq_refl Heq) as [_ Hafter_epoch].

  assert (Hversion_len :
    length (nat_to_le4 tx1.(tx_version)) =
    length (nat_to_le4 tx2.(tx_version))).
  { repeat rewrite nat_to_le4_length. reflexivity. }
  pose proof (app_inj_tail nat
    (nat_to_le4 tx1.(tx_version))
    (nat_to_le4 tx2.(tx_version))
    (hash_outpoints tx1.(tx_inputs) ++ hash_outputs tx1.(tx_outputs) ++
     [SPEND_TYPE_KEY_PATH] ++ serialize_spent_output s1 ++
     nat_to_le4 i1 ++ nat_to_le4 tx1.(tx_locktime))
    (hash_outpoints tx2.(tx_inputs) ++ hash_outputs tx2.(tx_outputs) ++
     [SPEND_TYPE_KEY_PATH] ++ serialize_spent_output s2 ++
     nat_to_le4 i2 ++ nat_to_le4 tx2.(tx_locktime))
    Hversion_len Hafter_epoch) as [Hversion_bytes Hafter_version].
  assert (Hversion : tx1.(tx_version) = tx2.(tx_version)).
  { eapply nat_to_le4_injective; eauto. }

  pose proof (hash_outpoints_length tx1.(tx_inputs)) as Hhop_len1.
  pose proof (hash_outpoints_length tx2.(tx_inputs)) as Hhop_len2.
  assert (Hhop_len :
    length (hash_outpoints tx1.(tx_inputs)) =
    length (hash_outpoints tx2.(tx_inputs))) by lia.
  pose proof (app_inj_tail nat
    (hash_outpoints tx1.(tx_inputs))
    (hash_outpoints tx2.(tx_inputs))
    (hash_outputs tx1.(tx_outputs) ++ [SPEND_TYPE_KEY_PATH] ++
     serialize_spent_output s1 ++ nat_to_le4 i1 ++ nat_to_le4 tx1.(tx_locktime))
    (hash_outputs tx2.(tx_outputs) ++ [SPEND_TYPE_KEY_PATH] ++
     serialize_spent_output s2 ++ nat_to_le4 i2 ++ nat_to_le4 tx2.(tx_locktime))
    Hhop_len Hafter_version) as [Hhash_outpoints Hafter_outpoints].
  assert (Hinput_outpoints :
    tx_input_outpoints tx1 = tx_input_outpoints tx2).
  { unfold tx_input_outpoints.
    eapply hash_outpoints_injective; eauto. }

  pose proof (hash_outputs_length tx1.(tx_outputs)) as Hhout_len1.
  pose proof (hash_outputs_length tx2.(tx_outputs)) as Hhout_len2.
  assert (Hhout_len :
    length (hash_outputs tx1.(tx_outputs)) =
    length (hash_outputs tx2.(tx_outputs))) by lia.
  pose proof (app_inj_tail nat
    (hash_outputs tx1.(tx_outputs))
    (hash_outputs tx2.(tx_outputs))
    ([SPEND_TYPE_KEY_PATH] ++ serialize_spent_output s1 ++
     nat_to_le4 i1 ++ nat_to_le4 tx1.(tx_locktime))
    ([SPEND_TYPE_KEY_PATH] ++ serialize_spent_output s2 ++
     nat_to_le4 i2 ++ nat_to_le4 tx2.(tx_locktime))
    Hhout_len Hafter_outpoints) as [Hhash_outputs Hafter_outputs].
  assert (Houtputs : tx1.(tx_outputs) = tx2.(tx_outputs)).
  { eapply hash_outputs_injective; eauto. }

  pose proof (app_inj_tail nat [SPEND_TYPE_KEY_PATH] [SPEND_TYPE_KEY_PATH]
    (serialize_spent_output s1 ++ nat_to_le4 i1 ++ nat_to_le4 tx1.(tx_locktime))
    (serialize_spent_output s2 ++ nat_to_le4 i2 ++ nat_to_le4 tx2.(tx_locktime))
    eq_refl Hafter_outputs) as [_ Hafter_spend_type].

  pose proof (serialize_spent_output_length s1 Hs1) as Hspent_len1.
  pose proof (serialize_spent_output_length s2 Hs2) as Hspent_len2.
  assert (Hspent_len :
    length (serialize_spent_output s1) =
    length (serialize_spent_output s2)) by lia.
  pose proof (app_inj_tail nat
    (serialize_spent_output s1)
    (serialize_spent_output s2)
    (nat_to_le4 i1 ++ nat_to_le4 tx1.(tx_locktime))
    (nat_to_le4 i2 ++ nat_to_le4 tx2.(tx_locktime))
    Hspent_len Hafter_spend_type) as [Hspent_bytes Hafter_spent].
  assert (Hspent : s1 = s2).
  { eapply serialize_spent_output_injective; eauto. }

  assert (Hindex_len :
    length (nat_to_le4 i1) = length (nat_to_le4 i2)).
  { repeat rewrite nat_to_le4_length. reflexivity. }
  pose proof (app_inj_tail nat
    (nat_to_le4 i1)
    (nat_to_le4 i2)
    (nat_to_le4 tx1.(tx_locktime))
    (nat_to_le4 tx2.(tx_locktime))
    Hindex_len Hafter_spent) as [Hindex_bytes Hlocktime_bytes].
  assert (Hindex : i1 = i2).
  { eapply nat_to_le4_injective; eauto. }
  assert (Hlocktime : tx1.(tx_locktime) = tx2.(tx_locktime)).
  { eapply nat_to_le4_injective; eauto. }

  subst s2.
  repeat split; try assumption; reflexivity.
Qed.

(** ** Property 2: Cross-Input Separation *)
Theorem sighash_cross_input_separation : forall tx i1 i2 s,
  wf_transaction tx ->
  wf_spent_output s ->
  i1 < pow2_32 ->
  i2 < pow2_32 ->
  i1 <> i2 ->
  sighash_v2 tx i1 s <> sighash_v2 tx i2 s.
Proof.
  intros tx i1 i2 s Htx Hs Hi1 Hi2 Hneq Heq.
  apply sighash_v2_injective in Heq; try assumption.
  destruct Heq as [_ [_ [_ [_ [Hidx _]]]]].
  contradiction.
Qed.

(** ** Property 3: Field Coverage *)
Theorem sighash_field_coverage_version : forall tx i s v',
  wf_transaction tx ->
  wf_transaction (mkTransaction v' tx.(tx_inputs) tx.(tx_outputs) tx.(tx_locktime)) ->
  wf_spent_output s ->
  i < pow2_32 ->
  tx.(tx_version) <> v' ->
  sighash_v2 tx i s <> sighash_v2 (mkTransaction v' tx.(tx_inputs) tx.(tx_outputs) tx.(tx_locktime)) i s.
Proof.
  intros tx i s v' Htx Htx' Hs Hi Hneq Heq.
  apply sighash_v2_injective in Heq; try assumption.
  destruct Heq as [Hversion _].
  contradiction.
Qed.

(** ** Property 3: Field Coverage - Locktime *)
Theorem sighash_field_coverage_locktime : forall tx i s l',
  wf_transaction tx ->
  wf_transaction (mkTransaction tx.(tx_version) tx.(tx_inputs) tx.(tx_outputs) l') ->
  wf_spent_output s ->
  i < pow2_32 ->
  tx.(tx_locktime) <> l' ->
  sighash_v2 tx i s <> sighash_v2 (mkTransaction tx.(tx_version) tx.(tx_inputs) tx.(tx_outputs) l') i s.
Proof.
  intros tx i s l' Htx Htx' Hs Hi Hneq Heq.
  apply sighash_v2_injective in Heq; try assumption.
  destruct Heq as [_ [_ [_ [Hlock _]]]].
  contradiction.
Qed.

(** ** Property 3: Field Coverage - Spent Value *)
Theorem sighash_field_coverage_spent_value : forall tx i s v',
  wf_transaction tx ->
  wf_spent_output s ->
  wf_spent_output (mkSpentOutput s.(so_script_version) s.(so_commitment) v') ->
  i < pow2_32 ->
  s.(so_value) <> v' ->
  sighash_v2 tx i s <> sighash_v2 tx i (mkSpentOutput s.(so_script_version) s.(so_commitment) v').
Proof.
  intros tx i s v' Htx Hs Hs' Hi Hneq Heq.
  apply sighash_v2_injective in Heq; try assumption.
  destruct Heq as [_ [_ [_ [_ [_ [_ [_ Hvalue]]]]]]].
  contradiction.
Qed.

(** ** Property 3: Field Coverage - Spent Commitment *)
Theorem sighash_field_coverage_spent_commitment : forall tx i s c',
  wf_transaction tx ->
  wf_spent_output s ->
  wf_spent_output (mkSpentOutput s.(so_script_version) c' s.(so_value)) ->
  i < pow2_32 ->
  s.(so_commitment) <> c' ->
  sighash_v2 tx i s <> sighash_v2 tx i (mkSpentOutput s.(so_script_version) c' s.(so_value)).
Proof.
  intros tx i s c' Htx Hs Hs' Hi Hneq Heq.
  apply sighash_v2_injective in Heq; try assumption.
  destruct Heq as [_ [_ [_ [_ [_ [_ [Hcommitment _]]]]]]].
  contradiction.
Qed.

(** ** Property 3: Field Coverage - Input Outpoints *)
Theorem sighash_field_coverage_input_outpoints : forall tx i s inputs',
  wf_transaction tx ->
  wf_transaction (mkTransaction tx.(tx_version) inputs' tx.(tx_outputs) tx.(tx_locktime)) ->
  wf_spent_output s ->
  i < pow2_32 ->
  tx_input_outpoints tx <> map (fun inp => inp.(txi_outpoint)) inputs' ->
  sighash_v2 tx i s <> sighash_v2 (mkTransaction tx.(tx_version) inputs' tx.(tx_outputs) tx.(tx_locktime)) i s.
Proof.
  intros tx i s inputs' Htx Htx' Hs Hi Hneq Heq.
  apply sighash_v2_injective in Heq; try assumption.
  destruct Heq as [_ [Hinputs _]].
  contradiction.
Qed.

(** ** Property 3: Field Coverage - Outputs *)
Theorem sighash_field_coverage_outputs : forall tx i s outputs',
  wf_transaction tx ->
  wf_transaction (mkTransaction tx.(tx_version) tx.(tx_inputs) outputs' tx.(tx_locktime)) ->
  wf_spent_output s ->
  i < pow2_32 ->
  tx.(tx_outputs) <> outputs' ->
  sighash_v2 tx i s <> sighash_v2 (mkTransaction tx.(tx_version) tx.(tx_inputs) outputs' tx.(tx_locktime)) i s.
Proof.
  intros tx i s outputs' Htx Htx' Hs Hi Hneq Heq.
  apply sighash_v2_injective in Heq; try assumption.
  destruct Heq as [_ [_ [Houtputs _]]].
  contradiction.
Qed.

(** ** Property 3: Field Coverage - Spent Script Version *)
Theorem sighash_field_coverage_spent_script_version : forall tx i s sv',
  wf_transaction tx ->
  wf_spent_output s ->
  wf_spent_output (mkSpentOutput sv' s.(so_commitment) s.(so_value)) ->
  i < pow2_32 ->
  s.(so_script_version) <> sv' ->
  sighash_v2 tx i s <> sighash_v2 tx i (mkSpentOutput sv' s.(so_commitment) s.(so_value)).
Proof.
  intros tx i s sv' Htx Hs Hs' Hi Hneq Heq.
  apply sighash_v2_injective in Heq; try assumption.
  destruct Heq as [_ [_ [_ [_ [_ [Hscript _]]]]]].
  contradiction.
Qed.

(* ================================================================= *)
(* Part VI: Complete PO-4 Theorem                                    *)
(* ================================================================= *)

Record SighashCommitmentProperty : Type := mkSighashCommitment {
  sc_injectivity : forall tx1 tx2 i1 i2 s1 s2,
    wf_transaction tx1 ->
    wf_transaction tx2 ->
    wf_spent_output s1 ->
    wf_spent_output s2 ->
    i1 < pow2_32 ->
    i2 < pow2_32 ->
    sighash_v2 tx1 i1 s1 = sighash_v2 tx2 i2 s2 ->
    tx1.(tx_version) = tx2.(tx_version) /\
    tx_input_outpoints tx1 = tx_input_outpoints tx2 /\
    tx1.(tx_outputs) = tx2.(tx_outputs) /\
    tx1.(tx_locktime) = tx2.(tx_locktime) /\
    i1 = i2 /\
    s1 = s2;

  sc_cross_input : forall tx i1 i2 s,
    wf_transaction tx ->
    wf_spent_output s ->
    i1 < pow2_32 ->
    i2 < pow2_32 ->
    i1 <> i2 ->
    sighash_v2 tx i1 s <> sighash_v2 tx i2 s;

  sc_field_coverage : forall tx i s,
    wf_transaction tx ->
    wf_spent_output s ->
    i < pow2_32 ->
    (forall inputs',
      wf_transaction (mkTransaction tx.(tx_version) inputs' tx.(tx_outputs) tx.(tx_locktime)) ->
      tx_input_outpoints tx <> map (fun inp => inp.(txi_outpoint)) inputs' ->
      sighash_v2 tx i s <> sighash_v2 (mkTransaction tx.(tx_version) inputs' tx.(tx_outputs) tx.(tx_locktime)) i s) /\
    (forall outputs',
      wf_transaction (mkTransaction tx.(tx_version) tx.(tx_inputs) outputs' tx.(tx_locktime)) ->
      tx.(tx_outputs) <> outputs' ->
      sighash_v2 tx i s <> sighash_v2 (mkTransaction tx.(tx_version) tx.(tx_inputs) outputs' tx.(tx_locktime)) i s) /\
    (forall v',
      wf_transaction (mkTransaction v' tx.(tx_inputs) tx.(tx_outputs) tx.(tx_locktime)) ->
      tx.(tx_version) <> v' ->
      sighash_v2 tx i s <> sighash_v2 (mkTransaction v' tx.(tx_inputs) tx.(tx_outputs) tx.(tx_locktime)) i s) /\
    (forall l',
      wf_transaction (mkTransaction tx.(tx_version) tx.(tx_inputs) tx.(tx_outputs) l') ->
      tx.(tx_locktime) <> l' ->
      sighash_v2 tx i s <> sighash_v2 (mkTransaction tx.(tx_version) tx.(tx_inputs) tx.(tx_outputs) l') i s) /\
    (forall sv',
      wf_spent_output (mkSpentOutput sv' s.(so_commitment) s.(so_value)) ->
      s.(so_script_version) <> sv' ->
      sighash_v2 tx i s <> sighash_v2 tx i (mkSpentOutput sv' s.(so_commitment) s.(so_value))) /\
    (forall v',
      wf_spent_output (mkSpentOutput s.(so_script_version) s.(so_commitment) v') ->
      s.(so_value) <> v' ->
      sighash_v2 tx i s <> sighash_v2 tx i (mkSpentOutput s.(so_script_version) s.(so_commitment) v')) /\
    (forall c',
      wf_spent_output (mkSpentOutput s.(so_script_version) c' s.(so_value)) ->
      s.(so_commitment) <> c' ->
      sighash_v2 tx i s <> sighash_v2 tx i (mkSpentOutput s.(so_script_version) c' s.(so_value)))
}.

(** The verified theorem shape for the Sighash v2 commitment property. *)
Theorem sighash_v2_commitment_property : SighashCommitmentProperty.
Proof.
  apply mkSighashCommitment.
  - (* Injectivity *)
    intros tx1 tx2 i1 i2 s1 s2 Htx1 Htx2 Hs1 Hs2 Hi1 Hi2 Heq.
    pose proof (sighash_v2_injective tx1 tx2 i1 i2 s1 s2
      Htx1 Htx2 Hs1 Hs2 Hi1 Hi2 Heq) as Hinj.
    destruct Hinj as [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]].
    repeat split; try assumption.
    destruct s1, s2.
    simpl in *.
    subst. reflexivity.
  - (* Cross-input separation *)
    apply sighash_cross_input_separation.
  - (* Field coverage *)
    intros tx i s Htx Hs Hi.
    repeat split.
    + intros inputs' Htx' Hneq.
      apply sighash_field_coverage_input_outpoints; assumption.
    + intros outputs' Htx' Hneq.
      apply sighash_field_coverage_outputs; assumption.
    + intros v' Htx' Hneq.
      apply sighash_field_coverage_version; assumption.
    + intros l' Htx' Hneq.
      apply sighash_field_coverage_locktime; assumption.
    + intros sv' Hs' Hneq.
      apply sighash_field_coverage_spent_script_version; assumption.
    + intros v' Hs' Hneq.
      apply sighash_field_coverage_spent_value; assumption.
    + intros c' Hs' Hneq.
      apply sighash_field_coverage_spent_commitment; assumption.
Qed.

(* ================================================================= *)
(* Summary                                                            *)
(* ================================================================= *)

(**
 * PO-4: Sighash Commitment Property - VERIFIED MODEL
 *
 * The SighashV2 module mechanizes the sighash v2 construction and proves the
 * commitment theorem shape under the SHA-256 collision-resistance axiom:
 *
 * 1. Injectivity (Theorem sighash_v2_injective):
 *    Equal sighashes imply equal consensus-significant transaction fields,
 *    input outpoints, input indices, and spent outputs.
 *
 * 2. Cross-Input Separation (Theorem sighash_cross_input_separation):
 *    Different u32 input indices always produce different sighashes.
 *
 * 3. Field Coverage (the sighash_field_coverage theorem family):
 *    Changing any consensus-critical field changes the sighash.
 *
 * These properties are combined in the SighashCommitmentProperty record. The
 * central [sighash_v2_injective] theorem, little-endian lemmas, fixed-width
 * serialization injectivity lemmas, and field coverage lemmas are
 * machine-checked. All commitment claims are scoped to well-formed
 * transactions, spent outputs, and u32 input indices with fixed-width consensus
 * fields.
 *
 * Dependencies:
 *   - SHA-256 collision resistance (axiomatized)
 *   - Tagged hash domain separation (by construction)
 *   - Little-endian encoding injectivity (machine-checked)
 *)

Definition PO4_verified_model : bool := true.
