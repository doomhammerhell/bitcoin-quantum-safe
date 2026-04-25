(** * VarintConcrete: Concrete Varint Implementation

    Discharges the 6 varint axioms from [SpendPredPQ.v] by providing
    a concrete implementation. This establishes PO-8: the axiom system
    is consistent (satisfiable) and provides a reference implementation.

    The concrete model uses a single-byte encoding:
      encode_len(n) = [n]
      decode_len([v | rest]) = Some(v, 1)

    This is the simplest model satisfying all 6 axioms. The axioms
    capture *interface* properties (round-trip, canonicality, prefix
    determinism) that hold for any correct varint encoding, including
    Bitcoin's compact-size format. The single-byte model demonstrates
    that the axiom system is not vacuously true (i.e., it has a model).
*)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
Import ListNotations.

(* ================================================================= *)
(** * Part I: Concrete Implementation                                  *)
(* ================================================================= *)

(** Encode a natural number as a single-byte varint. *)
Definition encode_len_impl (n : nat) : list nat := [n].

(** Decode a varint from the front of a byte list.
    Returns [Some (value, bytes_consumed)] or [None]. *)
Definition decode_len_impl (bs : list nat) : option (nat * nat) :=
  match bs with
  | [] => None
  | v :: _ => Some (v, 1)
  end.

(* ================================================================= *)
(** * Part II: Axiom Discharge — All 6 Axioms Hold                     *)
(* ================================================================= *)

(** ** Axiom 1: Round-trip *)
(** Decoding an encoded value recovers the original value and the
    encoding length. *)
Theorem decode_encode_len_impl : forall (n : nat),
  decode_len_impl (encode_len_impl n) = Some (n, length (encode_len_impl n)).
Proof.
  intros n. simpl. reflexivity.
Qed.

(** ** Axiom 2: Positive encoding length *)
(** Every encoding produces at least one byte. *)
Theorem encode_len_pos_impl : forall (n : nat),
  length (encode_len_impl n) >= 1.
Proof.
  intros n. simpl. lia.
Qed.

(** ** Axiom 3: Decode with trailing data *)
(** Decoding succeeds when the encoded bytes are followed by arbitrary
    trailing data, and the result is the same as without trailing data. *)
Theorem decode_len_app_impl : forall (n : nat) (tail : list nat),
  decode_len_impl (encode_len_impl n ++ tail) = Some (n, length (encode_len_impl n)).
Proof.
  intros n tail. simpl. reflexivity.
Qed.

(** ** Axiom 4: Decode determines a prefix *)
(** If decoding succeeds, the consumed bytes form a prefix of the input. *)
Theorem decode_len_prefix_impl : forall (bs : list nat) (v consumed : nat),
  decode_len_impl bs = Some (v, consumed) ->
  consumed <= length bs.
Proof.
  intros bs v consumed Hdec.
  destruct bs as [| b rest]; simpl in *.
  - discriminate.
  - injection Hdec as Hv Hc. subst. simpl. lia.
Qed.

(** ** Axiom 5: Canonical uniqueness *)
(** If decoding a list [bs] succeeds with value [v], then the first
    [consumed] bytes of [bs] equal [encode_len_impl v]. *)
Theorem decode_len_canonical_impl : forall (bs : list nat) (v consumed : nat),
  decode_len_impl bs = Some (v, consumed) ->
  firstn consumed bs = encode_len_impl v.
Proof.
  intros bs v consumed Hdec.
  destruct bs as [| b rest]; simpl in *.
  - discriminate.
  - injection Hdec as Hv Hc. subst. simpl. reflexivity.
Qed.

(** ** Axiom 6: Consumed equals encoding length *)
(** If decoding succeeds, the number of bytes consumed equals the
    length of the canonical encoding. *)
Theorem decode_len_consumed_eq_impl : forall (bs : list nat) (v consumed : nat),
  decode_len_impl bs = Some (v, consumed) ->
  consumed = length (encode_len_impl v).
Proof.
  intros bs v consumed Hdec.
  destruct bs as [| b rest]; simpl in *.
  - discriminate.
  - injection Hdec as Hv Hc. subst. simpl. reflexivity.
Qed.

(* ================================================================= *)
(** * Part III: Consistency Witness                                     *)
(* ================================================================= *)

(** The existence of a concrete model satisfying all 6 axioms proves
    that the axiom system in [SpendPredPQ.v] is consistent. This is
    important because inconsistent axioms would allow proving anything,
    making the entire development vacuous.

    We package the 6 theorems as a record to make the correspondence
    explicit. *)

Record VarintAxioms (enc : nat -> list nat) (dec : list nat -> option (nat * nat)) : Prop := {
  va_round_trip : forall n, dec (enc n) = Some (n, length (enc n));
  va_pos : forall n, length (enc n) >= 1;
  va_app : forall n tail, dec (enc n ++ tail) = Some (n, length (enc n));
  va_prefix : forall bs v c, dec bs = Some (v, c) -> c <= length bs;
  va_canonical : forall bs v c, dec bs = Some (v, c) -> firstn c bs = enc v;
  va_consumed_eq : forall bs v c, dec bs = Some (v, c) -> c = length (enc v);
}.

(** The concrete implementation satisfies all varint axioms. *)
Theorem varint_axioms_satisfied :
  VarintAxioms encode_len_impl decode_len_impl.
Proof.
  constructor.
  - exact decode_encode_len_impl.
  - exact encode_len_pos_impl.
  - exact decode_len_app_impl.
  - exact decode_len_prefix_impl.
  - exact decode_len_canonical_impl.
  - exact decode_len_consumed_eq_impl.
Qed.

(* ================================================================= *)
(** * Part IV: Derived Properties                                      *)
(* ================================================================= *)

(** We can also prove additional properties that follow from the axioms
    and hold for the concrete implementation. *)

(** Encoding is injective: different values produce different encodings. *)
Theorem encode_len_injective : forall (n m : nat),
  encode_len_impl n = encode_len_impl m -> n = m.
Proof.
  intros n m H. simpl in H. injection H. auto.
Qed.

(** Decoding is deterministic (trivially, as a Coq function). *)
Theorem decode_len_deterministic : forall (bs : list nat),
  decode_len_impl bs = decode_len_impl bs.
Proof.
  reflexivity.
Qed.

(** Encoding followed by decoding is an identity on the value. *)
Theorem encode_decode_value : forall (n : nat),
  match decode_len_impl (encode_len_impl n) with
  | Some (v, _) => v = n
  | None => False
  end.
Proof.
  intros n. simpl. reflexivity.
Qed.

(** The encoding length is always exactly 1 for this concrete model. *)
Theorem encode_len_impl_length : forall (n : nat),
  length (encode_len_impl n) = 1.
Proof.
  intros n. simpl. reflexivity.
Qed.

(* ================================================================= *)
(** * Part V: Integration with SpendPredPQ                             *)
(* ================================================================= *)

(** The concrete implementation can be used to instantiate the abstract
    [encode_len] and [decode_len] from [SpendPredPQ.v]. Since all 6
    axioms are satisfied, any theorem proved in [SpendPredPQ.v] using
    those axioms holds for this concrete model.

    In particular:
    - [parse_serialize_round_trip] holds with concrete varint
    - [parse_varint_injective] holds with concrete varint
    - [spend_pred_pq_anti_malleability] holds with concrete varint

    This provides PO-8 evidence: the axiomatized interface has at least
    one correct implementation, so the axioms are not contradictory. *)

(** Helper lemmas for list operations. *)

Lemma firstn_app_exact : forall {A : Type} (l1 l2 : list A),
  firstn (length l1) (l1 ++ l2) = l1.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma skipn_app_exact : forall {A : Type} (l1 l2 : list A),
  skipn (length l1) (l1 ++ l2) = l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - reflexivity.
  - apply IH.
Qed.

(** Concrete witness serialization using the single-byte varint. *)
Definition serialize_witness_concrete (pk sig : list nat) : list nat :=
  encode_len_impl (length pk) ++ pk ++ sig.

(** Concrete witness parsing using the single-byte varint. *)
Definition parse_witness_concrete (w : list nat) : option (list nat * list nat) :=
  match decode_len_impl w with
  | None => None
  | Some (pk_len, consumed) =>
    let rest := skipn consumed w in
    if Nat.leb pk_len (length rest) then
      let pk := firstn pk_len rest in
      let sig := skipn pk_len rest in
      match pk, sig with
      | [], _ => None
      | _, [] => None
      | _ :: _, _ :: _ => Some (pk, sig)
      end
    else
      None
  end.

(** Round-trip for the concrete implementation. *)
Theorem parse_serialize_concrete_round_trip :
  forall (pk sig : list nat),
    pk <> [] ->
    sig <> [] ->
    parse_witness_concrete (serialize_witness_concrete pk sig) = Some (pk, sig).
Proof.
  intros pk sig Hpk Hsig.
  unfold parse_witness_concrete, serialize_witness_concrete.
  simpl.
  (* After decode: pk_len = length pk, consumed = 1 *)
  (* rest = skipn 1 ([length pk] ++ pk ++ sig) = pk ++ sig *)
  (* Need: Nat.leb (length pk) (length (pk ++ sig)) = true *)
  assert (Hle : (length pk <=? length (pk ++ sig)) = true).
  { rewrite Nat.leb_le. rewrite length_app. lia. }
  rewrite Hle.
  rewrite firstn_app_exact.
  rewrite skipn_app_exact.
  destruct pk as [| ph pt].
  - exfalso. apply Hpk. reflexivity.
  - destruct sig as [| sh st].
    + exfalso. apply Hsig. reflexivity.
    + reflexivity.
Qed.

(* ================================================================= *)
(** * Summary                                                          *)
(* ================================================================= *)

(**
    PO-8: Axiom Consistency (Varint Model)

    1. [decode_encode_len_impl]: Axiom 1 — round-trip
    2. [encode_len_pos_impl]: Axiom 2 — positive encoding length
    3. [decode_len_app_impl]: Axiom 3 — decode with trailing data
    4. [decode_len_prefix_impl]: Axiom 4 — decode determines prefix
    5. [decode_len_canonical_impl]: Axiom 5 — canonical uniqueness
    6. [decode_len_consumed_eq_impl]: Axiom 6 — consumed = |encode(v)|
    7. [varint_axioms_satisfied]: all 6 axioms packaged as a record

    Derived properties:
    8.  [encode_len_injective]: encoding is injective
    9.  [decode_len_deterministic]: decoding is deterministic
    10. [encode_decode_value]: encode-decode identity on values
    11. [parse_serialize_concrete_round_trip]: witness round-trip

    Correspondence:
    - Axioms match [SpendPredPQ.v] (A1–A6)
    - Concrete model demonstrates axiom consistency
    - Witness parse/serialize matches [SpendPredPQ.v] structure
*)
