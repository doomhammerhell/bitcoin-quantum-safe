(* WitnessExtraction: Coq→OCaml extraction for bounded PO-8 evidence
 *
 * This module exposes the varint-based witness encoding functions and
 * consensus-domain witness predicates for OCaml extraction. The current formal
 * model covers compact-size values through 0xFD/u16; source-level Rust proof
 * remains outside this artifact.
 *
 * Copyright (c) 2026 Mayckon Giovani. MIT License.
 *)

From Coq Require Import Extraction.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import PeanoNat.
From Coq Require Import String.
Import ListNotations.

(* Import existing verified modules - use BitcoinPQ namespace *)
From BitcoinPQ Require Import VarintConcrete.

(* ================================================================= *)
(* Extraction configuration                                          *)
(* ================================================================= *)

(* Extract native Coq types to OCaml equivalents *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive prod => "( * )" [ "(,)" ].

(* Extract nat to int for efficiency (witness sizes are bounded) *)
Extract Inductive nat => int [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(* Native extraction for arithmetic used by the bounded refinement harness. *)
Extract Inlined Constant Nat.add => "( + )".
Extract Inlined Constant Nat.mul => "( * )".
Extract Inlined Constant Init.Nat.add => "( + )".
Extract Inlined Constant Init.Nat.mul => "( * )".
Extract Constant Nat.leb => "( <= )".
Extract Constant Nat.eqb => "( = )".
Extract Constant Nat.div => "( / )".
Extract Constant Nat.modulo => "( mod )".

Extract Constant compact_single_max => "252".
Extract Constant compact_fd_marker => "253".
Extract Constant byte_max => "255".
Extract Constant byte_base => "256".
Extract Constant max_u16 => "65535".
Extract Constant max_witness_size => "16000".

(* ================================================================= *)
(* Witness encoding functions for extraction                         *)
(* ================================================================= *)

(* Encode a nat using the modeled Bitcoin compact-size varint range. *)
Definition encode_varint_nat (n : nat) : list nat :=
  encode_len_multi n.

(* Decode a varint from a byte list in the modeled range. *)
Definition decode_varint_nat (data : list nat) : option (nat * nat) :=
  decode_len_multi data.

(* Serialize a witness: pk_len || pk || sig_len || sig *)
Definition serialize_witness_extract (pk : list nat) (sig : list nat) : list nat :=
  serialize_witness_concrete pk sig.

(* Parse a witness into (pk, sig) option *)
Definition parse_witness_extract (w : list nat) : option (list nat * list nat) :=
  parse_witness_concrete w.

Fixpoint list_nat_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && list_nat_eqb xs' ys'
  | _, _ => false
  end.

Lemma list_nat_eqb_eq : forall xs ys,
  list_nat_eqb xs ys = true <-> xs = ys.
Proof.
  induction xs as [| x xs IH]; destruct ys as [| y ys]; simpl.
  - split; auto.
  - split; discriminate.
  - split; discriminate.
  - rewrite andb_true_iff. rewrite Nat.eqb_eq. rewrite IH.
    split.
    + intros [Hxy Htail]. subst. reflexivity.
    + intros H. injection H as Hxy Htail. auto.
Qed.

(* Check whether a witness is the canonical concrete encoding of [pk, sig]. *)
Definition is_canonical_witness_extract (pk : list nat) (sig : list nat) (w : list nat) : bool :=
  match parse_witness_concrete w with
  | Some (parsed_pk, parsed_sig) =>
      list_nat_eqb parsed_pk pk &&
      list_nat_eqb parsed_sig sig &&
      list_nat_eqb w (serialize_witness_concrete pk sig)
  | None => false
  end.

(* Rust's public canonicality predicate only takes witness bytes. This extracted
   predicate is the Coq-side observational counterpart of [is_canonical_witness]
   in [src/encoding.rs]. *)
Definition is_canonical_witness_bytes_extract (w : list nat) : bool :=
  is_canonical_witness_concrete_bytes w.

(* Consensus-domain parser: Rust consensus validation rejects witnesses above
   MAX_WITNESS_SIZE before parsing. This extracted function is the Coq-side
   counterpart of [parse_consensus_witness] in [src/encoding.rs]. *)
Definition parse_consensus_witness_extract
    (w : list nat) : option (list nat * list nat) :=
  parse_consensus_witness_concrete w.

Definition is_canonical_consensus_witness_bytes_extract (w : list nat) : bool :=
  is_canonical_consensus_witness_concrete_bytes w.

Theorem is_canonical_witness_extract_sound :
  forall pk sig w,
    is_canonical_witness_extract pk sig w = true ->
    parse_witness_concrete w = Some (pk, sig) /\
    w = serialize_witness_concrete pk sig.
Proof.
  intros pk sig w Hcanon.
  unfold is_canonical_witness_extract in Hcanon.
  destruct (parse_witness_concrete w) as [[parsed_pk parsed_sig] |] eqn:Hparse;
    try discriminate.
  repeat rewrite andb_true_iff in Hcanon.
  destruct Hcanon as [[Hpk Hsig] Hw].
  apply list_nat_eqb_eq in Hpk.
  apply list_nat_eqb_eq in Hsig.
  apply list_nat_eqb_eq in Hw.
  subst parsed_pk parsed_sig.
  split.
  - reflexivity.
  - exact Hw.
Qed.

Theorem is_canonical_witness_bytes_extract_sound :
  forall w,
    is_canonical_witness_bytes_extract w = true ->
    exists pk sig,
      parse_witness_concrete w = Some (pk, sig) /\
      w = serialize_witness_concrete pk sig.
Proof.
  exact is_canonical_witness_concrete_bytes_sound.
Qed.

Theorem parse_consensus_witness_extract_sound :
  forall w pk sig,
    parse_consensus_witness_extract w = Some (pk, sig) ->
    List.length w <= max_witness_size /\
    parse_witness_concrete w = Some (pk, sig).
Proof.
  exact parse_consensus_witness_concrete_sound.
Qed.

Theorem is_canonical_consensus_witness_bytes_extract_sound :
  forall w,
    is_canonical_consensus_witness_bytes_extract w = true ->
    List.length w <= max_witness_size /\
    exists pk sig,
      parse_witness_concrete w = Some (pk, sig) /\
      w = serialize_witness_concrete pk sig.
Proof.
  exact is_canonical_consensus_witness_concrete_bytes_sound.
Qed.

Definition parse_witness_trace_extract
    (w : list nat) : list nat * option (list nat * list nat) :=
  let start_trace := [1; List.length w] in
  match decode_len_multi w with
  | None => (start_trace ++ [2], None)
  | Some (pk_len, pk_consumed) =>
      let trace_after_pk_decode := start_trace ++ [3; pk_len; pk_consumed] in
      let rest_after_pk_len := skipn pk_consumed w in
      if Nat.leb pk_len (List.length rest_after_pk_len) then
        let pk := firstn pk_len rest_after_pk_len in
        let rest_after_pk := skipn pk_len rest_after_pk_len in
        let trace_after_pk :=
          trace_after_pk_decode ++ [6; pk_len; List.length rest_after_pk_len] in
        match decode_len_multi rest_after_pk with
        | None => (trace_after_pk ++ [7; List.length rest_after_pk], None)
        | Some (sig_len, sig_consumed) =>
            let trace_after_sig_decode :=
              trace_after_pk ++ [8; sig_len; sig_consumed] in
            let rest_after_sig_len := skipn sig_consumed rest_after_pk in
            if Nat.leb sig_len (List.length rest_after_sig_len) then
              let signature := firstn sig_len rest_after_sig_len in
              let trailing := skipn sig_len rest_after_sig_len in
              match pk, signature, trailing with
              | [], _, _ =>
                  (trace_after_sig_decode ++ [11; List.length pk; List.length signature], None)
              | _, [], _ =>
                  (trace_after_sig_decode ++ [11; List.length pk; List.length signature], None)
              | _ :: _, _ :: _, [] =>
                  (trace_after_sig_decode ++ [12; List.length pk; List.length signature],
                   Some (pk, signature))
              | _, _, _ :: _ =>
                  (trace_after_sig_decode ++
                     [10; sig_len; List.length rest_after_sig_len], None)
              end
            else
              (trace_after_sig_decode ++
                 [10; sig_len; List.length rest_after_sig_len], None)
        end
      else
        (trace_after_pk_decode ++ [5; pk_len; List.length rest_after_pk_len], None)
  end.

Theorem parse_witness_trace_extract_result :
  forall w,
    snd (parse_witness_trace_extract w) = parse_witness_concrete w.
Proof.
  intros w.
  unfold parse_witness_trace_extract, parse_witness_concrete.
  destruct (decode_len_multi w) as [[pk_len pk_consumed] |] eqn:Hpkdec;
    simpl; try reflexivity.
  destruct (pk_len <=? List.length (skipn pk_consumed w)) eqn:Hpkle;
    simpl; try reflexivity.
  destruct (decode_len_multi (skipn pk_len (skipn pk_consumed w)))
    as [[sig_len sig_consumed] |] eqn:Hsigdec;
    simpl; try reflexivity.
  destruct (sig_len <=?
    List.length (skipn sig_consumed (skipn pk_len (skipn pk_consumed w)))) eqn:Hsigle;
    simpl; try reflexivity.
  destruct (firstn pk_len (skipn pk_consumed w)) as [| pk_head pk_tail];
    simpl; try reflexivity.
  destruct (firstn sig_len
    (skipn sig_consumed (skipn pk_len (skipn pk_consumed w))))
    as [| sig_head sig_tail];
    simpl; try reflexivity.
  destruct (skipn sig_len
    (skipn sig_consumed (skipn pk_len (skipn pk_consumed w))))
    as [| trail_head trail_tail];
    reflexivity.
Qed.

(* ================================================================= *)
(* Extraction commands                                                *)
(* ================================================================= *)

(* Module encapsulation for extraction *)
Module WitnessExtraction.

  Definition extract_encode_varint := encode_len_multi.
  Definition extract_decode_varint := decode_len_multi.
  Definition extract_serialize_witness := serialize_witness_concrete.
  Definition extract_parse_witness := parse_witness_concrete.
  Definition extract_parse_consensus_witness := parse_consensus_witness_extract.
  Definition extract_is_canonical_witness := is_canonical_witness_extract.
  Definition extract_is_canonical_witness_bytes := is_canonical_witness_bytes_extract.
  Definition extract_is_canonical_consensus_witness_bytes :=
    is_canonical_consensus_witness_bytes_extract.
  Definition extract_parse_witness_trace := parse_witness_trace_extract.

End WitnessExtraction.

(* Extraction directives *)
Extraction Language OCaml.

(* Suppress extraction of standard library internals *)
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive sumor => "option" [ "Some" "None" ].
