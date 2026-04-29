(** * UTXOTransitions: Mechanized UTXO Transition System

    Copyright (c) 2026 Mayckon Giovani. MIT License.

    Corresponds to proof obligations PO-5 (transition determinism) and
    PO-7 (cost boundedness) from the paper "Toward Protocol-Level
    Quantum Safety in Bitcoin".

    We model the UTXO set as an association list and define the
    deterministic state transition function [delta_tx]. We prove:
      - PO-5: Transition determinism (same inputs → same output)
      - PO-5+: No-double-spend preservation across transitions
      - PO-7: Cost(tx) ≤ α · weight(tx) with α = 1

    The UTXO model is a simplified version of the TLA+ specification
    in [formal/tla/BitcoinPQ.tla] and the Rust implementation in
    [src/lib.rs]. The cost model matches [src/weight.rs].
*)

From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import PeanoNat.
From Coq Require Import Lia.
Import ListNotations.

(* ================================================================= *)
(** * Part I: UTXO Set Model                                          *)
(* ================================================================= *)

(** ** Core types *)

(** A transaction output stored in the UTXO set. *)
Record Output : Type := mkOutput {
  script_version : nat;
  value : nat;
}.

(** An outpoint is a natural number (simplified, matching TLA+ model). *)
Definition OutPoint := nat.

(** The UTXO set is an association list from outpoints to outputs. *)
Definition UtxoSet := list (nat * Output).

(** A transaction input references an outpoint. *)
Record TxInput : Type := mkTxInput {
  outpoint : nat;
}.

(** A transaction output as it appears in a transaction body. *)
Record TxOutput : Type := mkTxOutput {
  tx_script_version : nat;
  tx_value : nat;
}.

(** A transaction has inputs and outputs. *)
Record Transaction : Type := mkTransaction {
  inputs : list TxInput;
  outputs : list TxOutput;
}.

(** ** Association list operations *)

(** Lookup an outpoint in the UTXO set. *)
Fixpoint lookup (U : UtxoSet) (op : nat) : option Output :=
  match U with
  | [] => None
  | (k, v) :: rest =>
    if Nat.eqb k op then Some v else lookup rest op
  end.

(** Remove an outpoint from the UTXO set. *)
Fixpoint remove (U : UtxoSet) (op : nat) : UtxoSet :=
  match U with
  | [] => []
  | (k, v) :: rest =>
    if Nat.eqb k op then remove rest op
    else (k, v) :: remove rest op
  end.

(** Remove all outpoints referenced by a list of inputs. *)
Fixpoint remove_inputs (U : UtxoSet) (ins : list TxInput) : UtxoSet :=
  match ins with
  | [] => U
  | inp :: rest => remove_inputs (remove U (outpoint inp)) rest
  end.

(** Add new outputs to the UTXO set with sequential ids starting from [base]. *)
Fixpoint add_outputs (U : UtxoSet) (outs : list TxOutput) (base : nat) : UtxoSet :=
  match outs with
  | [] => U
  | o :: rest =>
    add_outputs (U ++ [(base, mkOutput (tx_script_version o) (tx_value o))]) rest (S base)
  end.

(** ** The UTXO state transition function *)

(** [delta_tx U tx fresh_id] applies transaction [tx] to UTXO set [U]:
    1. Remove all inputs from U
    2. Add all outputs with fresh ids starting from [fresh_id]

    The [fresh_id] parameter models the deterministic txid counter
    from the TLA+ specification ([nextId] in BitcoinPQ.tla). *)
Definition delta_tx (U : UtxoSet) (tx : Transaction) (fresh_id : nat) : UtxoSet :=
  let U' := remove_inputs U (inputs tx) in
  add_outputs U' (outputs tx) fresh_id.

(* ================================================================= *)
(** * Part II: PO-5 — Transition Determinism                          *)
(* ================================================================= *)

(** ** PO-5a: Reflexive determinism *)

(** The transition function is a pure Coq function, so applying it
    to identical arguments always produces identical results. *)
Theorem delta_tx_deterministic :
  forall (U : UtxoSet) (tx : Transaction) (fresh_id : nat),
    delta_tx U tx fresh_id = delta_tx U tx fresh_id.
Proof.
  reflexivity.
Qed.

(** ** PO-5b: Extensional determinism *)

(** If two UTXO sets, transactions, and fresh ids are equal, then
    the transition results are equal. This is the stronger form
    that matches the TLA+ model's determinism property. *)
Theorem delta_tx_deterministic_ext :
  forall (U1 U2 : UtxoSet) (tx1 tx2 : Transaction) (id1 id2 : nat),
    U1 = U2 -> tx1 = tx2 -> id1 = id2 ->
    delta_tx U1 tx1 id1 = delta_tx U2 tx2 id2.
Proof.
  intros U1 U2 tx1 tx2 id1 id2 HU Htx Hid.
  subst. reflexivity.
Qed.

(* ================================================================= *)
(** * Part III: No-Double-Spend Preservation                          *)
(* ================================================================= *)

(** A set of outpoints [spent] has "no double spend" w.r.t. [U] if
    none of the spent outpoints are in [U]. This matches the TLA+
    invariant [NoDoubleSpend: spent ∩ DOMAIN utxo = {}]. *)
Definition no_double_spend (U : UtxoSet) (spent : list nat) : Prop :=
  forall op, In op spent -> lookup U op = None.

(** ** Helper lemmas *)

Lemma lookup_remove_same : forall U op,
  lookup (remove U op) op = None.
Proof.
  induction U as [| [k v] rest IH]; intros op; simpl.
  - reflexivity.
  - destruct (Nat.eqb k op) eqn:Heq.
    + apply IH.
    + simpl. rewrite Heq. apply IH.
Qed.

Lemma lookup_remove_diff : forall U op1 op2,
  op1 <> op2 ->
  lookup (remove U op1) op2 = lookup U op2.
Proof.
  induction U as [| [k v] rest IH]; intros op1 op2 Hneq; simpl.
  - reflexivity.
  - destruct (Nat.eqb k op1) eqn:Heq1.
    + apply Nat.eqb_eq in Heq1. subst k.
      destruct (Nat.eqb op1 op2) eqn:Heq2.
      * apply Nat.eqb_eq in Heq2. exfalso. apply Hneq. exact Heq2.
      * apply IH. exact Hneq.
    + simpl. destruct (Nat.eqb k op2) eqn:Heq2.
      * reflexivity.
      * apply IH. exact Hneq.
Qed.

(** If lookup returns None, it stays None after removing more entries. *)
Lemma lookup_remove_none : forall U op1 op2,
  lookup U op2 = None ->
  lookup (remove U op1) op2 = None.
Proof.
  intros U op1 op2 Hnone.
  destruct (Nat.eq_dec op1 op2) as [Heq | Hneq].
  - subst. apply lookup_remove_same.
  - rewrite lookup_remove_diff; assumption.
Qed.

(** remove_inputs preserves lookup = None. *)
Lemma lookup_remove_inputs_none : forall ins U op,
  lookup U op = None ->
  lookup (remove_inputs U ins) op = None.
Proof.
  induction ins as [| inp rest IH]; intros U op Hnone; simpl.
  - exact Hnone.
  - apply IH. apply lookup_remove_none. exact Hnone.
Qed.

(** After remove_inputs, looking up a removed outpoint returns None. *)
Lemma lookup_remove_inputs_removed : forall ins U op,
  In op (map outpoint ins) ->
  lookup (remove_inputs U ins) op = None.
Proof.
  induction ins as [| inp rest IH]; intros U op Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + subst op.
      apply lookup_remove_inputs_none.
      apply lookup_remove_same.
    + apply IH. exact Hin.
Qed.

Lemma lookup_app_last : forall U k v op,
  op <> k ->
  lookup (U ++ [(k, v)]) op = lookup U op.
Proof.
  induction U as [| [k' v'] rest IH]; intros k v op Hneq; simpl.
  - destruct (Nat.eqb k op) eqn:Heq.
    + apply Nat.eqb_eq in Heq. exfalso. apply Hneq. symmetry. exact Heq.
    + reflexivity.
  - destruct (Nat.eqb k' op) eqn:Heq.
    + reflexivity.
    + apply IH. exact Hneq.
Qed.

Lemma lookup_add_outputs_old_general : forall outs U base op,
  (forall i, i < length outs -> op <> base + i) ->
  lookup (add_outputs U outs base) op = lookup U op.
Proof.
  induction outs as [| o rest IH]; intros U base op Hrange; simpl.
  - reflexivity.
  - rewrite IH.
    + rewrite lookup_app_last.
      * reflexivity.
      * specialize (Hrange 0).
        assert (H0 : 0 < S (length rest)) by lia.
        specialize (Hrange H0). rewrite Nat.add_0_r in Hrange. exact Hrange.
    + intros i Hi.
      specialize (Hrange (S i)).
      assert (HSi : S i < S (length rest)) by lia.
      specialize (Hrange HSi).
      lia.
Qed.

(** ** Main theorem: delta_tx preserves no-double-spend *)

(** After applying a transaction, the previously-spent outpoints plus
    the newly-spent inputs are all absent from the resulting UTXO set.
    This corresponds to the TLA+ invariant:
      [spent' ∩ DOMAIN utxo' = {}]

    We require:
    - All inputs exist in U (precondition for a valid transaction)
    - No duplicate inputs (standard Bitcoin consensus rule)
    - Fresh ids don't collide with spent outpoints
*)
Theorem delta_tx_preserves_no_double_spend :
  forall U tx fresh_id spent,
    no_double_spend U spent ->
    (forall inp, In inp (inputs tx) -> lookup U (outpoint inp) <> None) ->
    NoDup (map outpoint (inputs tx)) ->
    (* Fresh ids are above all spent outpoints *)
    (forall op, In op spent -> op < fresh_id) ->
    (* Fresh ids are above all input outpoints *)
    (forall inp, In inp (inputs tx) -> outpoint inp < fresh_id) ->
    no_double_spend (delta_tx U tx fresh_id) (spent ++ map outpoint (inputs tx)).
Proof.
  intros U tx fresh_id spent0 Hnds Hexist Hnodup Hfresh_spent Hfresh_inp.
  unfold no_double_spend, delta_tx.
  intros op Hin.
  apply in_app_iff in Hin.
  destruct Hin as [Hin_old | Hin_new].
  - (* op was already spent: lookup U op = None *)
    rewrite lookup_add_outputs_old_general.
    + apply lookup_remove_inputs_none. apply Hnds. exact Hin_old.
    + intros i Hi.
      specialize (Hfresh_spent op Hin_old). lia.
  - (* op is a newly spent input *)
    rewrite lookup_add_outputs_old_general.
    + apply lookup_remove_inputs_removed. exact Hin_new.
    + intros i Hi.
      apply in_map_iff in Hin_new.
      destruct Hin_new as [inp [Heq Hin_inp]].
      subst op.
      specialize (Hfresh_inp inp Hin_inp). lia.
Qed.

(* ================================================================= *)
(** * Part IV: PO-7 — Cost Boundedness                                *)
(* ================================================================= *)

(** The cost model matches [src/weight.rs]:
    - INPUT_OVERHEAD_WU = 144 (outpoint: 36 bytes × 4 WU/byte)
    - BASE_TX_OVERHEAD_WU = 40 (version + locktime + varints: 10 bytes × 4 WU/byte)
    - OUTPUT_WU = 164 (script_version + commitment + value: 41 bytes × 4 WU/byte)
    - NON_WITNESS_SCALE = 4
*)

(** Cost of a single input: witness bytes (at 1 WU/byte) + overhead. *)
Definition cost_input (witness_len : nat) : nat :=
  witness_len + 144.

(** Base weight of a transaction: fixed overhead + per-output cost. *)
Definition base_weight (num_outputs : nat) : nat :=
  40 + num_outputs * 164.

(** Total cost of a transaction. *)
Definition cost_tx (witness_lens : list nat) (num_outputs : nat) : nat :=
  fold_right (fun wl acc => cost_input wl + acc) 0 witness_lens + base_weight num_outputs.

(** Standard SegWit weight of a transaction.
    weight = non_witness_bytes × 4 + witness_bytes × 1
    non_witness_bytes = 10 + num_inputs × 36 + num_outputs × 41 *)
Definition weight_tx (num_inputs : nat) (witness_lens : list nat) (num_outputs : nat) : nat :=
  (10 + num_inputs * 36 + num_outputs * 41) * 4 + fold_right Nat.add 0 witness_lens.

(** ** Helper lemma: sum of (wl + 144) = sum of wl + n × 144 *)

Lemma fold_cost_input_eq : forall (wls : list nat),
  fold_right (fun wl acc => cost_input wl + acc) 0 wls =
  fold_right Nat.add 0 wls + length wls * 144.
Proof.
  unfold cost_input.
  induction wls as [| wl rest IH]; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

(** ** PO-7: Cost(tx) ≤ α · weight(tx) with α = 1 *)

(** The cost function is bounded by the weight function. Since α = 1,
    this states that Cost(tx) ≤ weight(tx).

    Proof sketch:
    - cost_tx = Σ(wl_i + 144) + 40 + num_outputs × 164
             = Σ wl_i + n × 144 + 40 + num_outputs × 164
    - weight_tx = (10 + n × 36 + num_outputs × 41) × 4 + Σ wl_i
               = 40 + n × 144 + num_outputs × 164 + Σ wl_i
    - So cost_tx = weight_tx, and the bound holds with equality.
*)
Theorem cost_bounded_by_weight :
  forall (witness_lens : list nat) (num_outputs : nat),
    cost_tx witness_lens num_outputs <= 1 * weight_tx (length witness_lens) witness_lens num_outputs.
Proof.
  intros witness_lens num_outputs.
  unfold cost_tx, weight_tx, base_weight.
  rewrite fold_cost_input_eq.
  rewrite Nat.mul_1_l.
  lia.
Qed.

(** Stronger result: cost equals weight (for this model). *)
Theorem cost_equals_weight :
  forall (witness_lens : list nat) (num_outputs : nat),
    cost_tx witness_lens num_outputs = weight_tx (length witness_lens) witness_lens num_outputs.
Proof.
  intros witness_lens num_outputs.
  unfold cost_tx, weight_tx, base_weight.
  rewrite fold_cost_input_eq.
  lia.
Qed.

(** ** Block cost invariant *)

(** C_MAX = 4,000,000 WU (matching src/params.rs). *)
Definition C_MAX : nat := 4000000.

(** Block cost: sum of transaction costs. *)
Definition block_cost (txs : list (list nat * nat)) : nat :=
  fold_right (fun tx acc => cost_tx (fst tx) (snd tx) + acc) 0 txs.

(** The block cost invariant: total cost ≤ C_MAX. *)
Definition check_block_cost (txs : list (list nat * nat)) : Prop :=
  block_cost txs <= C_MAX.

(** If the block cost invariant holds, then each transaction's cost
    is bounded by its weight (transitivity with PO-7). *)
Theorem block_cost_bounded_by_weights :
  forall (txs : list (list nat * nat)),
    check_block_cost txs ->
    forall wls nout,
      In (wls, nout) txs ->
      cost_tx wls nout <= weight_tx (length wls) wls nout.
Proof.
  intros txs _ wls nout _.
  pose proof (cost_bounded_by_weight wls nout) as H.
  rewrite Nat.mul_1_l in H. exact H.
Qed.

(* ================================================================= *)
(** * Summary of verified properties                                   *)
(* ================================================================= *)

(**
    PO-5: Transition Determinism
    1. [delta_tx_deterministic]: reflexive determinism
    2. [delta_tx_deterministic_ext]: extensional determinism
    3. [delta_tx_preserves_no_double_spend]: no-double-spend preservation

    PO-7: Cost Boundedness
    4. [cost_bounded_by_weight]: Cost(tx) ≤ 1 · weight(tx)
    5. [cost_equals_weight]: Cost(tx) = weight(tx) (exact equality)
    6. [block_cost_bounded_by_weights]: block invariant implies per-tx bound

    Correspondence to other artifacts:
    - UTXO model matches [formal/tla/BitcoinPQ.tla] (outpoint ids, delta)
    - Cost constants match [src/weight.rs] (144, 40, 164, 4)
    - Block cost invariant matches [src/params.rs] (C_MAX = 4,000,000)
*)
