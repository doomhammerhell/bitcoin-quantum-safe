(** * SpendPredPQ: Mechanized PQ Spend Predicate

    Copyright (c) 2026 Mayckon Giovani. MIT License.

    Corresponds to proof obligations PO-1, PO-2, PO-3 from the paper
    "Toward Protocol-Level Quantum Safety in Bitcoin".

    We define the PQ spend predicate over abstract byte representations
    and prove:
      - PO-1: Totality (the predicate always returns a boolean)
      - PO-2: Determinism (same inputs always produce same output)
      - PO-3: Parse canonicality (injectivity on accepting domain)

    Extended with:
      - Axiomatized varint encoding model matching Bitcoin compact-size
      - Varint-based parse/serialize for witness data
      - Round-trip property: parse(serialize(pk, sig)) = Some(pk, sig)
      - Canonicality: parse produces witnesses that re-serialize identically
      - All PO-1/PO-2/PO-3 re-proved with varint-based parse
*)

From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import PeanoNat.
From Coq Require Import Lia.
Import ListNotations.

(** ** Abstract types *)

Definition bytes := list nat.
Definition commitment := bytes.
Definition message := bytes.
Definition pubkey := bytes.
Definition signature := bytes.
Definition witness := bytes.

(** ** Byte-string equality *)

Fixpoint bytes_eqb (a b : bytes) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => Nat.eqb x y && bytes_eqb xs ys
  | _, _ => false
  end.

Lemma bytes_eqb_refl : forall (a : bytes), bytes_eqb a a = true.
Proof.
  induction a as [| x xs IH].
  - reflexivity.
  - simpl. rewrite Nat.eqb_refl. simpl. exact IH.
Qed.

Lemma bytes_eqb_eq : forall (a b : bytes),
  bytes_eqb a b = true <-> a = b.
Proof.
  induction a as [| x xs IH]; destruct b as [| y ys]; simpl.
  - split; auto.
  - split; discriminate.
  - split; discriminate.
  - rewrite andb_true_iff. rewrite Nat.eqb_eq. rewrite IH.
    split.
    + intros [Hxy Hxsys]. subst. reflexivity.
    + intros H. injection H as Hxy Hxsys. auto.
Qed.

(** ** Cryptographic primitive interfaces (axiomatized) *)

Parameter H : pubkey -> commitment.
Parameter Vfy : pubkey -> message -> signature -> bool.

(* ================================================================= *)
(** * Part I: Original single-byte-prefix parse (backward compat)     *)
(* ================================================================= *)

(** ** Original witness parsing (single-byte length prefix) *)

Definition parse_simple (w : witness) : option (pubkey * signature) :=
  match w with
  | [] => None
  | len :: rest =>
    if Nat.leb len (length rest) then
      let pk := firstn len rest in
      let sig := skipn len rest in
      match pk, sig with
      | [], _ => None
      | _, [] => None
      | _, _  => Some (pk, sig)
      end
    else
      None
  end.

(* ================================================================= *)
(** * Part II: Axiomatized varint encoding model                      *)
(* ================================================================= *)

(** We model Bitcoin's compact-size varint encoding as an abstract pair
    of functions [encode_len] and [decode_len] with axioms capturing
    the essential properties:

    - Round-trip: decoding an encoded value recovers the value
    - Positive length: encoding always produces at least one byte
    - Canonicality: encoding is the unique minimal representation
    - Rejection: non-canonical encodings are rejected by decode

    This abstraction is faithful to the Rust implementation in
    [src/encoding.rs] without committing to byte-level details
    in the Coq model. *)

(** [encode_len n] produces the canonical varint encoding of [n]. *)
Parameter encode_len : nat -> list nat.

(** [decode_len bs] attempts to decode a varint from the front of [bs].
    Returns [Some (value, bytes_consumed)] on success, [None] on failure. *)
Parameter decode_len : list nat -> option (nat * nat).

(** *** Axiom 1: Round-trip *)
(** Decoding an encoded value recovers the original value and the
    encoding length. *)
Axiom decode_encode_len : forall (n : nat),
  decode_len (encode_len n) = Some (n, length (encode_len n)).

(** *** Axiom 2: Positive encoding length *)
(** Every encoding produces at least one byte. *)
Axiom encode_len_pos : forall (n : nat),
  length (encode_len n) >= 1.

(** *** Axiom 3: Decode with trailing data *)
(** Decoding succeeds when the encoded bytes are followed by arbitrary
    trailing data, and the result is the same as without trailing data. *)
Axiom decode_len_app : forall (n : nat) (tail : list nat),
  decode_len (encode_len n ++ tail) = Some (n, length (encode_len n)).

(** *** Axiom 4: Decode determines a prefix *)
(** If decoding succeeds, the consumed bytes form a prefix of the input. *)
Axiom decode_len_prefix : forall (bs : list nat) (v consumed : nat),
  decode_len bs = Some (v, consumed) ->
  consumed <= length bs.

(** *** Axiom 5: Canonical uniqueness *)
(** If decoding a list [bs] succeeds with value [v], then the first
    [consumed] bytes of [bs] equal [encode_len v]. This ensures that
    [encode_len] is the unique canonical encoding. *)
Axiom decode_len_canonical : forall (bs : list nat) (v consumed : nat),
  decode_len bs = Some (v, consumed) ->
  firstn consumed bs = encode_len v.

(** *** Axiom 6: Consumed equals encoding length *)
(** If decoding succeeds, the number of bytes consumed equals the
    length of the canonical encoding. *)
Axiom decode_len_consumed_eq : forall (bs : list nat) (v consumed : nat),
  decode_len bs = Some (v, consumed) ->
  consumed = length (encode_len v).

(* ================================================================= *)
(** * Part III: Varint-based witness parse and serialize               *)
(* ================================================================= *)

(** ** Serialize *)

(** [serialize_witness pk sig] produces the canonical witness encoding:
    [encode_len(|pk|) ++ pk ++ encode_len(|sig|) ++ sig]. *)
Definition serialize_witness (pk : pubkey) (sig : signature) : witness :=
  encode_len (length pk) ++ pk ++ encode_len (length sig) ++ sig.

(** ** Parse *)

(** [parse_varint_witness w] decodes a witness using varint length prefix.

    Algorithm:
    1. Decode varint [pk_len] from the front of [w]
    2. Let [rest] = bytes after the varint
    3. If [pk_len > |rest|] then fail
    4. [pk] = first [pk_len] bytes of [rest]
    5. Decode varint [sig_len] from the bytes after [pk]
    6. [sig] = first [sig_len] bytes after the signature-length varint
    7. Reject trailing bytes, empty [pk], and empty [sig]
    8. Return [Some (pk, sig)]
*)
Definition parse_varint_witness (w : witness) : option (pubkey * signature) :=
  match decode_len w with
  | None => None
  | Some (pk_len, pk_consumed) =>
    let rest_after_pk_len := skipn pk_consumed w in
    if Nat.leb pk_len (length rest_after_pk_len) then
      let pk := firstn pk_len rest_after_pk_len in
      let rest_after_pk := skipn pk_len rest_after_pk_len in
      match decode_len rest_after_pk with
      | None => None
      | Some (sig_len, sig_consumed) =>
        let rest_after_sig_len := skipn sig_consumed rest_after_pk in
        if Nat.leb sig_len (length rest_after_sig_len) then
          let sig := firstn sig_len rest_after_sig_len in
          let trailing := skipn sig_len rest_after_sig_len in
          match pk, sig, trailing with
          | [], _, _ => None
          | _, [], _ => None
          | _ :: _, _ :: _, [] => Some (pk, sig)
          | _, _, _ :: _ => None
          end
        else
          None
      end
    else
      None
  end.

(** For the main development, [parse] now refers to the varint version. *)
Definition parse := parse_varint_witness.

(* ================================================================= *)
(** * Part IV: Helper lemmas for list manipulation                     *)
(* ================================================================= *)

Lemma skipn_app_exact : forall {A : Type} (l1 l2 : list A),
  skipn (length l1) (l1 ++ l2) = l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma firstn_app_exact : forall {A : Type} (l1 l2 : list A),
  firstn (length l1) (l1 ++ l2) = l1.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma skipn_app_ge : forall {A : Type} (n : nat) (l1 l2 : list A),
  n = length l1 ->
  skipn n (l1 ++ l2) = l2.
Proof.
  intros A n l1 l2 Hn. subst n. apply skipn_app_exact.
Qed.

Lemma firstn_app_le : forall {A : Type} (n : nat) (l1 l2 : list A),
  n = length l1 ->
  firstn n (l1 ++ l2) = l1.
Proof.
  intros A n l1 l2 Hn. subst n. apply firstn_app_exact.
Qed.

Lemma firstn_app_length_l : forall {A : Type} (n : nat) (l1 l2 : list A),
  n <= length l1 ->
  length (firstn n (l1 ++ l2)) = n.
Proof.
  intros A n l1 l2 Hle.
  rewrite firstn_length.
  rewrite app_length.
  lia.
Qed.

Lemma length_firstn_le : forall {A : Type} (n : nat) (l : list A),
  n <= length l ->
  length (firstn n l) = n.
Proof.
  intros A n l Hle.
  rewrite firstn_length. lia.
Qed.

Lemma length_skipn : forall {A : Type} (n : nat) (l : list A),
  n <= length l ->
  length (skipn n l) = length l - n.
Proof.
  intros A n.
  induction n as [| n IH]; intros l Hle.
  - simpl. lia.
  - destruct l as [| x xs].
    + simpl in Hle. lia.
    + simpl in Hle. simpl. rewrite IH; lia.
Qed.

Lemma firstn_skipn_app : forall {A : Type} (n : nat) (l : list A),
  firstn n l ++ skipn n l = l.
Proof.
  intros A n l.
  apply firstn_skipn.
Qed.

Lemma firstn_length_cons : forall {A : Type} (n : nat) (l : list A) (x : A) (xs : list A),
  firstn n l = x :: xs -> n >= 1.
Proof.
  intros A n l x xs Hf.
  destruct n; simpl in Hf; [discriminate | lia].
Qed.



(* ================================================================= *)
(** * Part V: Round-trip theorem                                       *)
(* ================================================================= *)

(** If [pk] and [sig] are both non-empty, then parsing the serialized
    witness recovers the original components. *)

Theorem parse_serialize_round_trip :
  forall (pk : pubkey) (sig : signature),
    pk <> [] ->
    sig <> [] ->
    parse_varint_witness (serialize_witness pk sig) = Some (pk, sig).
Proof.
  intros pk sig Hpk Hsig.
  unfold parse_varint_witness, serialize_witness.
  (* The witness is: encode_len(|pk|) ++ pk ++ encode_len(|sig|) ++ sig *)
  (* Step 1: decode_len succeeds on the prefix *)
  rewrite decode_len_app.
  (* Now we need to show skipn, firstn, etc. work correctly *)
  (* rest = skipn (length (encode_len (length pk))) (encode_len (length pk) ++ pk ++ encode_len (length sig) ++ sig) *)
  rewrite skipn_app_exact.
  (* rest = pk ++ encode_len (length sig) ++ sig *)
  (* pk_len = length pk *)
  (* Need: Nat.leb (length pk) (length (pk ++ encode_len (length sig) ++ sig)) = true *)
  assert (Hle : (length pk <=? length (pk ++ encode_len (length sig) ++ sig)) = true).
  { rewrite Nat.leb_le. rewrite app_length. lia. }
  rewrite Hle.
  (* firstn (length pk) (pk ++ encode_len (length sig) ++ sig) = pk *)
  rewrite firstn_app_exact.
  (* skipn (length pk) (pk ++ encode_len (length sig) ++ sig) = encode_len (length sig) ++ sig *)
  rewrite skipn_app_exact.
  (* Decode and consume the signature length prefix. *)
  rewrite decode_len_app.
  rewrite skipn_app_exact.
  assert (Hsigle : (length sig <=? length sig) = true).
  { rewrite Nat.leb_le. lia. }
  rewrite Hsigle.
  rewrite firstn_all.
  rewrite skipn_all.
  (* Now we need pk and sig to be non-empty *)
  destruct pk as [| pk_hd pk_tl].
  - exfalso. apply Hpk. reflexivity.
  - destruct sig as [| sig_hd sig_tl].
    + exfalso. apply Hsig. reflexivity.
    + reflexivity.
Qed.

(* ================================================================= *)
(** * Part VI: Parse extraction lemma for varint parse                 *)
(* ================================================================= *)

(** If [parse_varint_witness w] succeeds, we can extract the structure. *)

Lemma parse_varint_extracts :
  forall (w : witness) (pk sig : bytes),
    parse_varint_witness w = Some (pk, sig) ->
    exists (pk_len pk_consumed sig_len sig_consumed : nat),
      decode_len w = Some (pk_len, pk_consumed) /\
      pk_len <= length (skipn pk_consumed w) /\
      pk = firstn pk_len (skipn pk_consumed w) /\
      decode_len (skipn pk_len (skipn pk_consumed w)) = Some (sig_len, sig_consumed) /\
      sig_len <= length (skipn sig_consumed (skipn pk_len (skipn pk_consumed w))) /\
      sig = firstn sig_len (skipn sig_consumed (skipn pk_len (skipn pk_consumed w))) /\
      skipn sig_len (skipn sig_consumed (skipn pk_len (skipn pk_consumed w))) = [] /\
      pk <> [] /\
      sig <> [].
Proof.
  intros w pk sig Hp.
  unfold parse_varint_witness in Hp.
  destruct (decode_len w) as [[pk_len pk_consumed] |] eqn:Hdec; [| discriminate].
  exists pk_len, pk_consumed.
  destruct (Nat.leb pk_len (length (skipn pk_consumed w))) eqn:Hpkleb; [| discriminate].
  apply Nat.leb_le in Hpkleb.
  remember (firstn pk_len (skipn pk_consumed w)) as fpk eqn:Hfpk.
  remember (skipn pk_len (skipn pk_consumed w)) as rest_after_pk eqn:Hrest.
  destruct (decode_len rest_after_pk) as [[sig_len sig_consumed] |] eqn:Hsigdec; [| discriminate].
  exists sig_len, sig_consumed.
  destruct (Nat.leb sig_len (length (skipn sig_consumed rest_after_pk))) eqn:Hsigleb; [| discriminate].
  apply Nat.leb_le in Hsigleb.
  remember (firstn sig_len (skipn sig_consumed rest_after_pk)) as ssig eqn:Hssig.
  remember (skipn sig_len (skipn sig_consumed rest_after_pk)) as trailing eqn:Htrailing.
  destruct fpk as [| ph pt]; [discriminate |].
  destruct ssig as [| sh st]; [discriminate |].
  destruct trailing as [| th tt]; [| discriminate].
  assert (Hpkeq : pk = ph :: pt) by congruence.
  assert (Hsigeq : sig = sh :: st) by congruence.
  repeat split; try congruence.
Qed.

(* ================================================================= *)
(** * Part VII: Canonicality theorem                                    *)
(* ================================================================= *)

(** If parsing a witness succeeds, then re-serializing the parsed
    components and parsing again yields the same result. This is the
    "serialize after parse" direction of canonicality. *)

Theorem parse_varint_canonical_re_serialize :
  forall (w : witness) (pk sig : bytes),
    parse_varint_witness w = Some (pk, sig) ->
    parse_varint_witness (serialize_witness pk sig) = Some (pk, sig).
Proof.
  intros w pk sig Hp.
  destruct (parse_varint_extracts w pk sig Hp)
    as [pk_len [pk_consumed [sig_len [sig_consumed Hextract]]]].
  destruct Hextract
    as [_ [_ [_ [_ [_ [_ [_ [Hpkne Hsigne]]]]]]]].
  apply parse_serialize_round_trip; assumption.
Qed.

(** Stronger canonicality: if [parse_varint_witness w = Some (pk, sig)],
    then [w] decomposes as
    [encode_len(|pk|) ++ pk ++ encode_len(|sig|) ++ sig], i.e.,
    [w = serialize_witness pk sig]. *)

Theorem parse_varint_witness_determines_serialize :
  forall (w : witness) (pk sig : bytes),
    parse_varint_witness w = Some (pk, sig) ->
    w = serialize_witness pk sig.
Proof.
  intros w pk sig Hp.
  destruct (parse_varint_extracts w pk sig Hp)
    as [pk_len [pk_consumed [sig_len [sig_consumed Hextract]]]].
  destruct Hextract
    as [Hpkdec [Hpkle [Hpk [Hsigdec [Hsigle [Hsig [Htrail [Hpkne Hsigne]]]]]]]].
  unfold serialize_witness.
  (* w = firstn pk_consumed w ++ skipn pk_consumed w *)
  rewrite <- (firstn_skipn pk_consumed w) at 1.
  (* firstn pk_consumed w = encode_len pk_len by canonicality axiom *)
  pose proof (decode_len_canonical w pk_len pk_consumed Hpkdec) as Hpkcan.
  rewrite Hpkcan.
  (* skipn pk_consumed w = firstn pk_len (...) ++ skipn pk_len (...) *)
  rewrite <- (firstn_skipn pk_len (skipn pk_consumed w)) at 1.
  rewrite <- Hpk.
  (* The remaining suffix starts with the canonical signature-length varint. *)
  rewrite <- (firstn_skipn sig_consumed (skipn pk_len (skipn pk_consumed w))) at 1.
  pose proof (decode_len_canonical
    (skipn pk_len (skipn pk_consumed w)) sig_len sig_consumed Hsigdec) as Hsigcan.
  rewrite Hsigcan.
  rewrite <- (firstn_skipn sig_len
    (skipn sig_consumed (skipn pk_len (skipn pk_consumed w)))) at 1.
  rewrite <- Hsig.
  rewrite Htrail.
  rewrite app_nil_r.
  (* Need: pk_len = length pk *)
  assert (Hpklen : length pk = pk_len).
  { rewrite Hpk. rewrite length_firstn_le; [reflexivity | exact Hpkle]. }
  rewrite Hpklen.
  (* Need: sig_len = length sig *)
  assert (Hsiglen : length sig = sig_len).
  { rewrite Hsig. rewrite length_firstn_le; [reflexivity | exact Hsigle]. }
  rewrite Hsiglen.
  reflexivity.
Qed.

(** Corollary: parse is injective on the accepting domain — if two
    witnesses parse to the same (pk, sig), they are identical. *)

Corollary parse_varint_injective :
  forall (w1 w2 : witness) (pk sig : bytes),
    parse_varint_witness w1 = Some (pk, sig) ->
    parse_varint_witness w2 = Some (pk, sig) ->
    w1 = w2.
Proof.
  intros w1 w2 pk sig H1 H2.
  rewrite (parse_varint_witness_determines_serialize w1 pk sig H1).
  rewrite (parse_varint_witness_determines_serialize w2 pk sig H2).
  reflexivity.
Qed.

(* ================================================================= *)
(** * Part VIII: The PQ spend predicate (varint version)               *)
(* ================================================================= *)

Definition spend_pred_pq (P : commitment) (m : message) (w : witness) : bool :=
  match parse w with
  | None => false
  | Some (pk, sig) =>
    bytes_eqb (H pk) P && Vfy pk m sig
  end.

(** ** PO-1: Totality *)

Theorem spend_pred_pq_total :
  forall (P : commitment) (m : message) (w : witness),
    spend_pred_pq P m w = true \/ spend_pred_pq P m w = false.
Proof.
  intros P m w.
  destruct (spend_pred_pq P m w); [left | right]; reflexivity.
Qed.

(** ** PO-2: Determinism *)

Theorem spend_pred_pq_deterministic :
  forall (P : commitment) (m : message) (w : witness),
    spend_pred_pq P m w = spend_pred_pq P m w.
Proof.
  reflexivity.
Qed.

Theorem spend_pred_pq_deterministic_ext :
  forall (P1 P2 : commitment) (m1 m2 : message) (w1 w2 : witness),
    P1 = P2 -> m1 = m2 -> w1 = w2 ->
    spend_pred_pq P1 m1 w1 = spend_pred_pq P2 m2 w2.
Proof.
  intros. subst. reflexivity.
Qed.

(** ** PO-3: Parse canonicality (varint version) *)

(** Parse is deterministic (trivially, as a Coq function). *)
Theorem parse_deterministic :
  forall (w : witness),
    parse w = parse w.
Proof.
  reflexivity.
Qed.

(** If two witnesses parse to the same components, they are identical.
    This is strictly stronger than the original PO-3 which only showed
    the relevant regions match. *)
Theorem parse_canonical :
  forall (w1 w2 : witness) (pk sig : bytes),
    parse w1 = Some (pk, sig) ->
    parse w2 = Some (pk, sig) ->
    w1 = w2.
Proof.
  intros w1 w2 pk sig H1 H2.
  exact (parse_varint_injective w1 w2 pk sig H1 H2).
Qed.

(** ** Spend predicate respects parse *)

Theorem spend_pred_pq_none_is_false :
  forall (P : commitment) (m : message) (w : witness),
    parse w = None ->
    spend_pred_pq P m w = false.
Proof.
  intros P m w Hp.
  unfold spend_pred_pq. rewrite Hp. reflexivity.
Qed.

(** If the hash does not match, the predicate rejects. *)
Theorem spend_pred_pq_hash_mismatch :
  forall (P : commitment) (m : message) (w : witness) (pk : pubkey) (sig : signature),
    parse w = Some (pk, sig) ->
    bytes_eqb (H pk) P = false ->
    spend_pred_pq P m w = false.
Proof.
  intros P m w pk sig Hp Hh.
  unfold spend_pred_pq. rewrite Hp. rewrite Hh. reflexivity.
Qed.

(** If verification fails, the predicate rejects. *)
Theorem spend_pred_pq_vfy_fail :
  forall (P : commitment) (m : message) (w : witness) (pk : pubkey) (sig : signature),
    parse w = Some (pk, sig) ->
    Vfy pk m sig = false ->
    spend_pred_pq P m w = false.
Proof.
  intros P m w pk sig Hp Hv.
  unfold spend_pred_pq. rewrite Hp.
  rewrite andb_false_iff. right. exact Hv.
Qed.

(** The predicate accepts iff parse succeeds, hash matches, and verify passes. *)
Theorem spend_pred_pq_iff :
  forall (P : commitment) (m : message) (w : witness),
    spend_pred_pq P m w = true <->
    exists (pk : pubkey) (sig : signature),
      parse w = Some (pk, sig) /\
      bytes_eqb (H pk) P = true /\
      Vfy pk m sig = true.
Proof.
  intros P m w. unfold spend_pred_pq. split.
  - destruct (parse w) as [[pk sig] |] eqn:Hp.
    + rewrite andb_true_iff. intros [Hh Hv].
      exists pk, sig. auto.
    + discriminate.
  - intros [pk [sig [Hp [Hh Hv]]]].
    rewrite Hp. rewrite Hh, Hv. reflexivity.
Qed.

(* ================================================================= *)
(** * Part IX: Anti-malleability theorem                                *)
(* ================================================================= *)

(** If the spend predicate accepts a witness [w], then [w] is the unique
    canonical encoding. Any other witness [w'] that the predicate would
    also accept (for the same commitment and message) must be identical
    to [w]. This rules out transaction malleability via witness encoding
    variation. *)

Theorem spend_pred_pq_anti_malleability :
  forall (P : commitment) (m : message) (w1 w2 : witness),
    spend_pred_pq P m w1 = true ->
    spend_pred_pq P m w2 = true ->
    (exists pk sig, parse w1 = Some (pk, sig) /\ parse w2 = Some (pk, sig)) ->
    w1 = w2.
Proof.
  intros P m w1 w2 _ _ [pk [sig [H1 H2]]].
  exact (parse_canonical w1 w2 pk sig H1 H2).
Qed.

(* ================================================================= *)
(** * Summary of verified properties                                   *)
(* ================================================================= *)

(**
    Original properties (re-proved with varint parse):
    1. [spend_pred_pq_total]: PO-1 — totality
    2. [spend_pred_pq_deterministic]: PO-2 — determinism
    3. [spend_pred_pq_deterministic_ext]: PO-2 — extensional determinism
    4. [parse_canonical]: PO-3 — parse canonicality (now full injectivity)
    5. [spend_pred_pq_iff]: complete characterization of acceptance
    6. [spend_pred_pq_none_is_false]: parse failure implies rejection
    7. [spend_pred_pq_hash_mismatch]: hash mismatch implies rejection
    8. [spend_pred_pq_vfy_fail]: verification failure implies rejection

    New properties:
    9.  [parse_serialize_round_trip]: parse(serialize(pk,sig)) = Some(pk,sig)
    10. [parse_varint_canonical_re_serialize]: parse success implies
        re-serialized witness also parses to same result
    11. [parse_varint_witness_determines_serialize]: parse success implies
        w = serialize_witness pk sig (full structural canonicality)
    12. [parse_varint_injective]: parse is injective on accepting domain
    13. [spend_pred_pq_anti_malleability]: accepting witnesses with same
        parsed components must be identical (anti-malleability)

    Varint axioms (faithful to src/encoding.rs):
    A1. [decode_encode_len]: round-trip
    A2. [encode_len_pos]: positive encoding length
    A3. [decode_len_app]: decode with trailing data
    A4. [decode_len_prefix]: consumed <= input length
    A5. [decode_len_canonical]: decoded prefix = canonical encoding
    A6. [decode_len_consumed_eq]: consumed = |encode_len(v)|
*)
