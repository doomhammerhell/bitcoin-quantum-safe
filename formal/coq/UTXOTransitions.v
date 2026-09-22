(** * UTXOTransitions: Mechanized UTXO Transition System

    Copyright (c) 2026 Mayckon Giovani. MIT License.

    Corresponds to proof obligations PO-5 (transition determinism) and
    PO-7 (cost boundedness) from the paper "Toward Protocol-Level
    Quantum Safety in Bitcoin".

    We model the UTXO set as an association list and define the
    deterministic state transition function [delta_tx]. We prove:
      - PO-5: Transition determinism (same inputs → same output)
      - PO-5+: No-double-spend preservation across transitions
      - PO-6: Structural UTXO-domain and total-value invariant preservation
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
(** * Part II: Executable Structural Validation Model                  *)
(* ================================================================= *)

(** The Rust [valid_tx] implementation contains cryptographic witness
    validation for PQ spends. The structural model below intentionally stops
    at the deterministic consensus state-machine boundary: duplicate-input
    rejection, input existence, value conservation, migration rules, and freeze
    rules. This is the extraction boundary used by the transition refinement
    harness; cryptographic spend-predicate correspondence is handled by the
    PO-8 and PO-4 artifacts. *)

Record MigrationConfig : Type := mkMigrationConfig {
  announcement_height : nat;
  cutover_height : nat;
}.

Definition is_pq_script_version (version : nat) : bool :=
  Nat.eqb version 2.

Fixpoint contains_nat (x : nat) (xs : list nat) : bool :=
  match xs with
  | [] => false
  | y :: ys => Nat.eqb x y || contains_nat x ys
  end.

Fixpoint has_duplicate_nat (xs : list nat) : bool :=
  match xs with
  | [] => false
  | x :: rest => contains_nat x rest || has_duplicate_nat rest
  end.

Definition input_outpoints (tx : Transaction) : list nat :=
  map outpoint (inputs tx).

Definition has_duplicate_inputs (tx : Transaction) : bool :=
  has_duplicate_nat (input_outpoints tx).

Fixpoint sum_input_values (U : UtxoSet) (ins : list TxInput) : option nat :=
  match ins with
  | [] => Some 0
  | inp :: rest =>
      match lookup U (outpoint inp), sum_input_values U rest with
      | Some spent, Some rest_sum => Some (value spent + rest_sum)
      | _, _ => None
      end
  end.

Fixpoint sum_output_values (outs : list TxOutput) : nat :=
  match outs with
  | [] => 0
  | out :: rest => tx_value out + sum_output_values rest
  end.

Fixpoint all_outputs_pq (outs : list TxOutput) : bool :=
  match outs with
  | [] => true
  | out :: rest => is_pq_script_version (tx_script_version out) && all_outputs_pq rest
  end.

(** Migration/freeze helpers mirror the Rust helpers' missing-input behavior:
    missing inputs are ignored here because [valid_tx_structural] rejects them
    earlier through [sum_input_values]. *)
Fixpoint all_present_inputs_pq_or_missing (U : UtxoSet) (ins : list TxInput) : bool :=
  match ins with
  | [] => true
  | inp :: rest =>
      match lookup U (outpoint inp) with
      | Some spent => is_pq_script_version (script_version spent) && all_present_inputs_pq_or_missing U rest
      | None => all_present_inputs_pq_or_missing U rest
      end
  end.

Definition check_migration_rules_structural
    (height : nat) (tx : Transaction) (U : UtxoSet) (config : MigrationConfig) : bool :=
  ((height <? announcement_height config) || all_outputs_pq (outputs tx)) &&
  ((height <? cutover_height config) || all_present_inputs_pq_or_missing U (inputs tx)).

Definition check_no_frozen_inputs_structural
    (height : nat) (tx : Transaction) (U : UtxoSet) (config : MigrationConfig) : bool :=
  (height <? cutover_height config) || all_present_inputs_pq_or_missing U (inputs tx).

Definition valid_tx_structural
    (U : UtxoSet) (tx : Transaction) (height : nat) (config : MigrationConfig) : bool :=
  if has_duplicate_inputs tx then false
  else
    match sum_input_values U (inputs tx) with
    | None => false
    | Some input_sum =>
        (sum_output_values (outputs tx) <=? input_sum) &&
        check_migration_rules_structural height tx U config &&
        check_no_frozen_inputs_structural height tx U config
    end.

Theorem valid_tx_structural_deterministic :
  forall U tx height config,
    valid_tx_structural U tx height config =
    valid_tx_structural U tx height config.
Proof.
  reflexivity.
Qed.

(* ================================================================= *)
(** * Part III: PO-5 — Transition Determinism                         *)
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

(** Boolean block-cost checker for extraction. *)
Definition check_block_cost_bool (txs : list (list nat * nat)) : bool :=
  block_cost txs <=? C_MAX.

(** Structural transaction cost for the transition refinement model.
    [TxInput] intentionally omits witness bytes; this assigns zero witness
    length to each input. Separate PO-8 artifacts cover witness bytes. *)
Definition cost_tx_structural (tx : Transaction) : nat :=
  cost_tx (repeat 0 (length (inputs tx))) (length (outputs tx)).

Definition block_cost_structural (txs : list Transaction) : nat :=
  fold_right (fun tx acc => cost_tx_structural tx + acc) 0 txs.

Definition check_block_cost_structural (txs : list Transaction) : bool :=
  block_cost_structural txs <=? C_MAX.

Fixpoint valid_block_transitions_structural
    (U : UtxoSet)
    (txs : list Transaction)
    (height : nat)
    (config : MigrationConfig)
    (fresh_id : nat) : bool :=
  match txs with
  | [] => true
  | tx :: rest =>
      if valid_tx_structural U tx height config then
        valid_block_transitions_structural
          (delta_tx U tx fresh_id)
          rest
          height
          config
          (fresh_id + length (outputs tx))
      else false
  end.

Definition valid_block_structural
    (U : UtxoSet)
    (txs : list Transaction)
    (height : nat)
    (config : MigrationConfig)
    (fresh_id : nat) : bool :=
  valid_block_transitions_structural U txs height config fresh_id &&
  check_block_cost_structural txs.

(** Operational block-application semantics for extraction.

    [valid_block_structural] is the consensus predicate; the functions below
    expose the same transition semantics as an executable state transformer.
    This is the boundary used by the Rust refinement harness when comparing
    final UTXO states, not only accept/reject bits. *)
Fixpoint apply_block_transitions_structural
    (U : UtxoSet)
    (txs : list Transaction)
    (height : nat)
    (config : MigrationConfig)
    (fresh_id : nat) : option UtxoSet :=
  match txs with
  | [] => Some U
  | tx :: rest =>
      if valid_tx_structural U tx height config then
        apply_block_transitions_structural
          (delta_tx U tx fresh_id)
          rest
          height
          config
          (fresh_id + length (outputs tx))
      else None
  end.

Definition apply_valid_block_structural
    (U : UtxoSet)
    (txs : list Transaction)
    (height : nat)
    (config : MigrationConfig)
    (fresh_id : nat) : option UtxoSet :=
  match apply_block_transitions_structural U txs height config fresh_id with
  | Some U' =>
      if check_block_cost_structural txs then Some U' else None
  | None => None
  end.

Definition option_is_some {A : Type} (value : option A) : bool :=
  match value with
  | Some _ => true
  | None => false
  end.

(* ================================================================= *)
(** * Part V: PO-6 Structural UTXO-Domain Invariants                 *)
(* ================================================================= *)

(** The TLA+ model checks invariant preservation over finite executions.  The
    lemmas below add an unbounded Coq theorem for the extraction-facing
    structural block semantics: if the pre-state has a unique UTXO domain and
    the abstract fresh-id range starts above every current outpoint, then
    sequential structural block application preserves a unique UTXO domain.

    This deliberately makes the txid/freshness boundary explicit.  In Rust,
    fresh IDs are [compute_txid(tx), vout]; proving that those never collide
    with live UTXO entries requires the SHA-256 collision-resistance / txid
    freshness assumption, not an association-list theorem. *)

Definition utxo_domain (U : UtxoSet) : list nat :=
  map fst U.

Definition domain_below (U : UtxoSet) (bound : nat) : Prop :=
  forall op, In op (utxo_domain U) -> op < bound.

Fixpoint all_lt_nat (xs : list nat) (bound : nat) : bool :=
  match xs with
  | [] => true
  | x :: rest => (x <? bound) && all_lt_nat rest bound
  end.

Definition domain_below_bool (U : UtxoSet) (bound : nat) : bool :=
  all_lt_nat (utxo_domain U) bound.

Definition domain_has_no_duplicates (U : UtxoSet) : bool :=
  negb (has_duplicate_nat (utxo_domain U)).

Fixpoint block_output_count (txs : list Transaction) : nat :=
  match txs with
  | [] => 0
  | tx :: rest => length (outputs tx) + block_output_count rest
  end.

Definition block_input_outpoints (txs : list Transaction) : list nat :=
  flat_map input_outpoints txs.

Fixpoint all_absent_from_utxo (U : UtxoSet) (ops : list nat) : bool :=
  match ops with
  | [] => true
  | op :: rest =>
      match lookup U op with
      | Some _ => false
      | None => all_absent_from_utxo U rest
      end
  end.

Definition spent_inputs_absent_bool (U : UtxoSet) (txs : list Transaction) : bool :=
  all_absent_from_utxo U (block_input_outpoints txs).

(** Total value carried by a UTXO set.  This is an economic invariant over the
    structural transition boundary: a structurally valid transaction may burn
    value as fee, but must not create value. *)
Fixpoint utxo_total_value (U : UtxoSet) : nat :=
  match U with
  | [] => 0
  | (_, out) :: rest => value out + utxo_total_value rest
  end.

(** Legacy/freeze observables used by the PO-6 migration monotonicity layer.
    Script version 2 is the unique PQ version in this abstract model; every
    other version is legacy/taproot-like authorization state. *)
Definition is_legacy_script_version (version : nat) : bool :=
  negb (is_pq_script_version version).

Definition output_is_legacy (out : Output) : bool :=
  is_legacy_script_version (script_version out).

Definition tx_output_is_legacy (out : TxOutput) : bool :=
  is_legacy_script_version (tx_script_version out).

Fixpoint legacy_utxo_count (U : UtxoSet) : nat :=
  match U with
  | [] => 0
  | (_, out) :: rest =>
      (if output_is_legacy out then 1 else 0) + legacy_utxo_count rest
  end.

Fixpoint legacy_tx_output_count (outs : list TxOutput) : nat :=
  match outs with
  | [] => 0
  | out :: rest =>
      (if tx_output_is_legacy out then 1 else 0) + legacy_tx_output_count rest
  end.

Definition frozen_utxo_count
    (height : nat) (config : MigrationConfig) (U : UtxoSet) : nat :=
  if height <? cutover_height config then 0 else legacy_utxo_count U.

Fixpoint accepted_block_inputs_pq_or_missing
    (U : UtxoSet)
    (txs : list Transaction)
    (height : nat)
    (config : MigrationConfig)
    (fresh_id : nat) : bool :=
  match txs with
  | [] => true
  | tx :: rest =>
      if valid_tx_structural U tx height config then
        all_present_inputs_pq_or_missing U (inputs tx) &&
        accepted_block_inputs_pq_or_missing
          (delta_tx U tx fresh_id)
          rest
          height
          config
          (fresh_id + length (outputs tx))
      else true
  end.

Lemma in_domain_remove : forall U removed op,
  In op (utxo_domain (remove U removed)) ->
  In op (utxo_domain U).
Proof.
  induction U as [| [k v] rest IH]; intros removed op Hin; simpl in *.
  - exact Hin.
  - destruct (Nat.eqb k removed) eqn:Heq.
    + right. apply (IH removed op). exact Hin.
    + simpl in Hin. destruct Hin as [Heq_op | Hin].
      * left. exact Heq_op.
      * right. apply (IH removed op). exact Hin.
Qed.

Lemma domain_remove_nodup : forall U removed,
  NoDup (utxo_domain U) ->
  NoDup (utxo_domain (remove U removed)).
Proof.
  induction U as [| [k v] rest IH]; intros removed Hnodup; simpl in *.
  - constructor.
  - inversion Hnodup as [| ? ? Hnotin Hrest_nodup]; subst.
    destruct (Nat.eqb k removed) eqn:Heq.
    + apply IH. exact Hrest_nodup.
    + simpl. constructor.
      * intros Hin.
        apply Hnotin.
        apply in_domain_remove with (removed := removed).
        exact Hin.
      * apply IH. exact Hrest_nodup.
Qed.

Lemma domain_remove_below : forall U removed bound,
  domain_below U bound ->
  domain_below (remove U removed) bound.
Proof.
  unfold domain_below.
  intros U removed bound Hbelow op Hin.
  apply Hbelow.
  apply in_domain_remove with (removed := removed).
  exact Hin.
Qed.

Lemma domain_remove_inputs_nodup : forall ins U,
  NoDup (utxo_domain U) ->
  NoDup (utxo_domain (remove_inputs U ins)).
Proof.
  induction ins as [| inp rest IH]; intros U Hnodup; simpl.
  - exact Hnodup.
  - apply IH. apply domain_remove_nodup. exact Hnodup.
Qed.

Lemma domain_remove_inputs_below : forall ins U bound,
  domain_below U bound ->
  domain_below (remove_inputs U ins) bound.
Proof.
  induction ins as [| inp rest IH]; intros U bound Hbelow; simpl.
  - exact Hbelow.
  - apply IH. apply domain_remove_below. exact Hbelow.
Qed.

Lemma domain_app_single : forall U k v,
  utxo_domain (U ++ [(k, v)]) = utxo_domain U ++ [k].
Proof.
  induction U as [| [k' v'] rest IH]; intros k v; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma domain_add_outputs : forall outs U base,
  utxo_domain (add_outputs U outs base) =
  utxo_domain U ++ seq base (length outs).
Proof.
  induction outs as [| out rest IH]; intros U base; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH.
    rewrite domain_app_single.
    rewrite <- app_assoc.
    simpl. reflexivity.
Qed.

Lemma seq_nodup : forall start len,
  NoDup (seq start len).
Proof.
  intros start len. revert start.
  induction len as [| len IH]; intros base; simpl.
  - constructor.
  - constructor.
    + intros Hin. apply in_seq in Hin. lia.
    + apply IH.
Qed.

Lemma NoDup_app_disjoint : forall (xs ys : list nat),
  NoDup xs ->
  NoDup ys ->
  (forall x, In x xs -> In x ys -> False) ->
  NoDup (xs ++ ys).
Proof.
  induction xs as [| x xs IH]; intros ys Hxs Hys Hdisjoint; simpl.
  - exact Hys.
  - inversion Hxs as [| ? ? Hnotin Hxs_nodup]; subst.
    constructor.
    + intros Hin.
      apply in_app_iff in Hin.
      destruct Hin as [Hin_xs | Hin_ys].
      * apply Hnotin. exact Hin_xs.
      * apply (Hdisjoint x).
        -- left. reflexivity.
        -- exact Hin_ys.
    + apply IH.
      * exact Hxs_nodup.
      * exact Hys.
      * intros y Hy Hiny.
        apply (Hdisjoint y).
        -- right. exact Hy.
        -- exact Hiny.
Qed.

Lemma domain_add_outputs_nodup : forall outs U base,
  NoDup (utxo_domain U) ->
  domain_below U base ->
  NoDup (utxo_domain (add_outputs U outs base)).
Proof.
  intros outs U base Hnodup Hbelow.
  rewrite domain_add_outputs.
  apply NoDup_app_disjoint.
  - exact Hnodup.
  - apply seq_nodup.
  - intros op Hin_domain Hin_seq.
    unfold domain_below in Hbelow.
    specialize (Hbelow op Hin_domain).
    apply in_seq in Hin_seq.
    lia.
Qed.

Lemma domain_add_outputs_below : forall outs U base,
  domain_below U base ->
  domain_below (add_outputs U outs base) (base + length outs).
Proof.
  unfold domain_below.
  intros outs U base Hbelow op Hin.
  rewrite domain_add_outputs in Hin.
  apply in_app_iff in Hin.
  destruct Hin as [Hin_old | Hin_new].
  - specialize (Hbelow op Hin_old). lia.
  - apply in_seq in Hin_new. lia.
Qed.

Theorem delta_tx_preserves_domain_nodup :
  forall U tx fresh_id,
    NoDup (utxo_domain U) ->
    domain_below U fresh_id ->
    NoDup (utxo_domain (delta_tx U tx fresh_id)).
Proof.
  intros U tx fresh_id Hnodup Hbelow.
  unfold delta_tx.
  apply domain_add_outputs_nodup.
  - apply domain_remove_inputs_nodup. exact Hnodup.
  - apply domain_remove_inputs_below. exact Hbelow.
Qed.

Theorem delta_tx_preserves_domain_bound :
  forall U tx fresh_id,
    domain_below U fresh_id ->
    domain_below (delta_tx U tx fresh_id) (fresh_id + length (outputs tx)).
Proof.
  intros U tx fresh_id Hbelow.
  unfold delta_tx.
  apply domain_add_outputs_below.
  apply domain_remove_inputs_below.
  exact Hbelow.
Qed.

Theorem apply_block_transitions_structural_preserves_domain_nodup :
  forall U txs height config fresh_id U',
    NoDup (utxo_domain U) ->
    domain_below U fresh_id ->
    apply_block_transitions_structural U txs height config fresh_id = Some U' ->
    NoDup (utxo_domain U') /\
    domain_below U' (fresh_id + block_output_count txs).
Proof.
  intros U txs. revert U.
  induction txs as [| tx rest IH]; intros U height config fresh_id U' Hnodup Hbelow Happly; simpl in *.
  - inversion Happly. subst U'. split.
    + exact Hnodup.
    + unfold domain_below in *. intros op Hin. specialize (Hbelow op Hin). lia.
  - destruct (valid_tx_structural U tx height config) eqn:Hvalid.
    + specialize
        (IH
           (delta_tx U tx fresh_id)
           height
           config
           (fresh_id + length (outputs tx))
           U').
      assert (Hnext_nodup : NoDup (utxo_domain (delta_tx U tx fresh_id))).
      { apply delta_tx_preserves_domain_nodup; assumption. }
      assert
        (Hnext_below :
          domain_below
            (delta_tx U tx fresh_id)
            (fresh_id + length (outputs tx))).
      { apply delta_tx_preserves_domain_bound. exact Hbelow. }
      specialize (IH Hnext_nodup Hnext_below Happly).
      destruct IH as [Hfinal_nodup Hfinal_below].
      split.
      * exact Hfinal_nodup.
      * unfold domain_below in *. intros op Hin.
        specialize (Hfinal_below op Hin). lia.
    + discriminate.
Qed.

Theorem apply_valid_block_structural_preserves_domain_nodup :
  forall U txs height config fresh_id U',
    NoDup (utxo_domain U) ->
    domain_below U fresh_id ->
    apply_valid_block_structural U txs height config fresh_id = Some U' ->
    NoDup (utxo_domain U') /\
    domain_below U' (fresh_id + block_output_count txs).
Proof.
  intros U txs height config fresh_id U' Hnodup Hbelow Happly.
  unfold apply_valid_block_structural in Happly.
  destruct (apply_block_transitions_structural U txs height config fresh_id)
    as [U_trans |] eqn:Htransitions.
  - destruct (check_block_cost_structural txs) eqn:Hcost.
    + inversion Happly. subst U_trans.
      eapply apply_block_transitions_structural_preserves_domain_nodup; eauto.
    + discriminate.
  - discriminate.
Qed.

Lemma contains_nat_false_not_in : forall x xs,
  contains_nat x xs = false ->
  ~ In x xs.
Proof.
  induction xs as [| y ys IH]; intros Hcontains Hin; simpl in *.
  - exact Hin.
  - apply Bool.orb_false_iff in Hcontains.
    destruct Hcontains as [Hhead Htail].
    destruct Hin as [Heq | Hin].
    + subst y. rewrite Nat.eqb_refl in Hhead. discriminate.
    + apply (IH Htail Hin).
Qed.

Lemma has_duplicate_nat_false_NoDup : forall xs,
  has_duplicate_nat xs = false ->
  NoDup xs.
Proof.
  induction xs as [| x rest IH]; intros Hdup; simpl in *.
  - constructor.
  - apply Bool.orb_false_iff in Hdup.
    destruct Hdup as [Hnotin Hrest].
    constructor.
    + apply contains_nat_false_not_in. exact Hnotin.
    + apply IH. exact Hrest.
Qed.

Lemma remove_not_in_domain : forall U op,
  ~ In op (utxo_domain U) ->
  remove U op = U.
Proof.
  induction U as [| [k v] rest IH]; intros op Hnotin; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb k op) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst k.
      exfalso. apply Hnotin. left. reflexivity.
    + f_equal. apply IH.
      intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma utxo_total_value_app_single : forall U k out,
  utxo_total_value (U ++ [(k, out)]) = utxo_total_value U + value out.
Proof.
  induction U as [| [k' out'] rest IH]; intros k out; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma utxo_total_value_add_outputs : forall outs U base,
  utxo_total_value (add_outputs U outs base) =
  utxo_total_value U + sum_output_values outs.
Proof.
  induction outs as [| out rest IH]; intros U base; simpl.
  - lia.
  - rewrite IH.
    rewrite utxo_total_value_app_single.
    simpl. lia.
Qed.

Lemma lookup_remove_value : forall U op out,
  NoDup (utxo_domain U) ->
  lookup U op = Some out ->
  value out + utxo_total_value (remove U op) = utxo_total_value U.
Proof.
  induction U as [| [k v] rest IH]; intros op out Hnodup Hlookup; simpl in *.
  - discriminate.
  - inversion Hnodup as [| ? ? Hnotin Hrest_nodup]; subst.
    destruct (Nat.eqb k op) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst k.
      inversion Hlookup. subst out.
      rewrite remove_not_in_domain.
      * lia.
      * exact Hnotin.
    + simpl.
      pose proof (IH op out Hrest_nodup Hlookup) as Hrest_value.
      lia.
Qed.

Lemma sum_input_values_remove_unmentioned : forall ins U op,
  ~ In op (map outpoint ins) ->
  sum_input_values (remove U op) ins = sum_input_values U ins.
Proof.
  induction ins as [| inp rest IH]; intros U op Hnotin; simpl in *.
  - reflexivity.
  - assert (Hneq : op <> outpoint inp).
    { intros Heq. apply Hnotin. left. symmetry. exact Heq. }
    rewrite lookup_remove_diff by exact Hneq.
    rewrite IH.
    + reflexivity.
    + intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma remove_inputs_value : forall ins U input_sum,
  NoDup (utxo_domain U) ->
  NoDup (map outpoint ins) ->
  sum_input_values U ins = Some input_sum ->
  utxo_total_value (remove_inputs U ins) + input_sum = utxo_total_value U.
Proof.
  induction ins as [| inp rest IH]; intros U input_sum Hdomain Hinputs Hsum; simpl in *.
  - inversion Hsum. lia.
  - inversion Hinputs as [| ? ? Hnotin_rest Hrest_nodup]; subst.
    destruct (lookup U (outpoint inp)) as [spent |] eqn:Hlookup; try discriminate.
    destruct (sum_input_values U rest) as [rest_sum |] eqn:Hrest_sum; try discriminate.
    inversion Hsum. subst input_sum.
    assert
      (Hrest_after_remove :
        sum_input_values (remove U (outpoint inp)) rest = Some rest_sum).
    {
      rewrite sum_input_values_remove_unmentioned.
      - exact Hrest_sum.
      - exact Hnotin_rest.
    }
    assert
      (Hremove_one :
        value spent + utxo_total_value (remove U (outpoint inp)) =
        utxo_total_value U).
    { apply lookup_remove_value; assumption. }
    specialize
      (IH
        (remove U (outpoint inp))
        rest_sum
        (domain_remove_nodup U (outpoint inp) Hdomain)
        Hrest_nodup
        Hrest_after_remove).
    lia.
Qed.

Theorem delta_tx_preserves_total_value :
  forall U tx height config fresh_id,
    NoDup (utxo_domain U) ->
    valid_tx_structural U tx height config = true ->
    utxo_total_value (delta_tx U tx fresh_id) <= utxo_total_value U.
Proof.
  intros U tx height config fresh_id Hdomain Hvalid.
  unfold valid_tx_structural in Hvalid.
  destruct (has_duplicate_inputs tx) eqn:Hdup; try discriminate.
  destruct (sum_input_values U (inputs tx)) as [input_sum |] eqn:Hinput_sum; try discriminate.
  apply Bool.andb_true_iff in Hvalid.
  destruct Hvalid as [Hvalue_and_migration _Hfreeze].
  apply Bool.andb_true_iff in Hvalue_and_migration.
  destruct Hvalue_and_migration as [Hvalue_bound _Hmigration].
  apply Nat.leb_le in Hvalue_bound.
  unfold delta_tx.
  rewrite utxo_total_value_add_outputs.
  assert (Hinput_nodup : NoDup (map outpoint (inputs tx))).
  {
    unfold has_duplicate_inputs in Hdup.
    apply has_duplicate_nat_false_NoDup. exact Hdup.
  }
  pose proof
    (remove_inputs_value
      (inputs tx)
      U
      input_sum
      Hdomain
      Hinput_nodup
      Hinput_sum)
    as Hremoved.
  lia.
Qed.

Theorem apply_block_transitions_structural_preserves_total_value :
  forall U txs height config fresh_id U',
    NoDup (utxo_domain U) ->
    domain_below U fresh_id ->
    apply_block_transitions_structural U txs height config fresh_id = Some U' ->
    utxo_total_value U' <= utxo_total_value U.
Proof.
  intros U txs. revert U.
  induction txs as [| tx rest IH]; intros U height config fresh_id U' Hdomain Hbelow Happly; simpl in *.
  - inversion Happly. subst U'. lia.
  - destruct (valid_tx_structural U tx height config) eqn:Hvalid; try discriminate.
    assert (Hdelta_value : utxo_total_value (delta_tx U tx fresh_id) <= utxo_total_value U).
    { eapply delta_tx_preserves_total_value; eauto. }
    assert (Hdelta_domain : NoDup (utxo_domain (delta_tx U tx fresh_id))).
    { apply delta_tx_preserves_domain_nodup; assumption. }
    assert
      (Hdelta_below :
        domain_below (delta_tx U tx fresh_id) (fresh_id + length (outputs tx))).
    { apply delta_tx_preserves_domain_bound. exact Hbelow. }
    specialize
      (IH
        (delta_tx U tx fresh_id)
        height
        config
        (fresh_id + length (outputs tx))
        U'
        Hdelta_domain
        Hdelta_below
        Happly).
    lia.
Qed.

Theorem apply_valid_block_structural_preserves_total_value :
  forall U txs height config fresh_id U',
    NoDup (utxo_domain U) ->
    domain_below U fresh_id ->
    apply_valid_block_structural U txs height config fresh_id = Some U' ->
    utxo_total_value U' <= utxo_total_value U.
Proof.
  intros U txs height config fresh_id U' Hdomain Hbelow Happly.
  unfold apply_valid_block_structural in Happly.
  destruct (apply_block_transitions_structural U txs height config fresh_id)
    as [U_trans |] eqn:Htransitions; try discriminate.
  destruct (check_block_cost_structural txs) eqn:Hcost; try discriminate.
  inversion Happly. subst U_trans.
  eapply apply_block_transitions_structural_preserves_total_value; eauto.
Qed.

(** Migration/freeze monotonicity.  These theorems strengthen PO-6 beyond
    generic domain/value preservation by connecting the executable
    migration/freeze predicates to structural state observables. *)

Lemma all_outputs_pq_legacy_count_zero : forall outs,
  all_outputs_pq outs = true ->
  legacy_tx_output_count outs = 0.
Proof.
  induction outs as [| out rest IH]; intros Hall; simpl in *.
  - reflexivity.
  - apply Bool.andb_true_iff in Hall.
    destruct Hall as [Hout Hrest].
    unfold tx_output_is_legacy, is_legacy_script_version.
    rewrite Hout.
    simpl.
    apply IH in Hrest.
    lia.
Qed.

Theorem valid_tx_structural_outputs_pq_after_announcement :
  forall U tx height config,
    valid_tx_structural U tx height config = true ->
    announcement_height config <= height ->
    all_outputs_pq (outputs tx) = true.
Proof.
  intros U tx height config Hvalid Hannounced.
  unfold valid_tx_structural in Hvalid.
  destruct (has_duplicate_inputs tx) eqn:Hdup; try discriminate.
  destruct (sum_input_values U (inputs tx)) as [input_sum |] eqn:Hinput_sum; try discriminate.
  apply Bool.andb_true_iff in Hvalid.
  destruct Hvalid as [Hvalue_and_migration _Hfreeze].
  apply Bool.andb_true_iff in Hvalue_and_migration.
  destruct Hvalue_and_migration as [_Hvalue_bound Hmigration].
  unfold check_migration_rules_structural in Hmigration.
  apply Bool.andb_true_iff in Hmigration.
  destruct Hmigration as [Houtputs _Hinputs].
  apply Bool.orb_true_iff in Houtputs.
  destruct Houtputs as [Hpre_activation | Hpq_outputs].
  - apply Nat.ltb_lt in Hpre_activation. lia.
  - exact Hpq_outputs.
Qed.

Theorem valid_tx_structural_no_legacy_outputs_after_announcement :
  forall U tx height config,
    valid_tx_structural U tx height config = true ->
    announcement_height config <= height ->
    legacy_tx_output_count (outputs tx) = 0.
Proof.
  intros U tx height config Hvalid Hannounced.
  apply all_outputs_pq_legacy_count_zero.
  eapply valid_tx_structural_outputs_pq_after_announcement; eauto.
Qed.

Theorem valid_tx_structural_inputs_pq_after_cutover :
  forall U tx height config,
    valid_tx_structural U tx height config = true ->
    cutover_height config <= height ->
    all_present_inputs_pq_or_missing U (inputs tx) = true.
Proof.
  intros U tx height config Hvalid Hcutover.
  unfold valid_tx_structural in Hvalid.
  destruct (has_duplicate_inputs tx) eqn:Hdup; try discriminate.
  destruct (sum_input_values U (inputs tx)) as [input_sum |] eqn:Hinput_sum; try discriminate.
  apply Bool.andb_true_iff in Hvalid.
  destruct Hvalid as [_Hvalue_and_migration Hfreeze].
  unfold check_no_frozen_inputs_structural in Hfreeze.
  apply Bool.orb_true_iff in Hfreeze.
  destruct Hfreeze as [Hpre_cutover | Hpq_inputs].
  - apply Nat.ltb_lt in Hpre_cutover. lia.
  - exact Hpq_inputs.
Qed.

Theorem apply_block_transitions_structural_inputs_pq_after_cutover :
  forall U txs height config fresh_id U',
    cutover_height config <= height ->
    apply_block_transitions_structural U txs height config fresh_id = Some U' ->
    accepted_block_inputs_pq_or_missing U txs height config fresh_id = true.
Proof.
  intros U txs. revert U.
  induction txs as [| tx rest IH]; intros U height config fresh_id U' Hcutover Happly; simpl in *.
  - reflexivity.
  - destruct (valid_tx_structural U tx height config) eqn:Hvalid; try discriminate.
    apply Bool.andb_true_iff. split.
    + eapply valid_tx_structural_inputs_pq_after_cutover; eauto.
    + eapply IH; eauto.
Qed.

Theorem apply_valid_block_structural_inputs_pq_after_cutover :
  forall U txs height config fresh_id U',
    cutover_height config <= height ->
    apply_valid_block_structural U txs height config fresh_id = Some U' ->
    accepted_block_inputs_pq_or_missing U txs height config fresh_id = true.
Proof.
  intros U txs height config fresh_id U' Hcutover Happly.
  unfold apply_valid_block_structural in Happly.
  destruct (apply_block_transitions_structural U txs height config fresh_id)
    as [U_trans |] eqn:Htransitions; try discriminate.
  destruct (check_block_cost_structural txs) eqn:Hcost; try discriminate.
  inversion Happly. subst U_trans.
  eapply apply_block_transitions_structural_inputs_pq_after_cutover; eauto.
Qed.

Lemma legacy_utxo_count_remove_le : forall U op,
  legacy_utxo_count (remove U op) <= legacy_utxo_count U.
Proof.
  induction U as [| [k out] rest IH]; intros op; simpl.
  - lia.
  - specialize (IH op).
    destruct (Nat.eqb k op) eqn:Heq.
    + destruct (output_is_legacy out) eqn:Hlegacy.
      * simpl.
        apply Nat.le_trans with (m := legacy_utxo_count rest).
        -- exact IH.
        -- lia.
      * simpl. exact IH.
    + destruct (output_is_legacy out) eqn:Hlegacy.
      * simpl. rewrite Hlegacy.
        replace (S (legacy_utxo_count rest)) with (1 + legacy_utxo_count rest) by lia.
        apply Nat.add_le_mono_l. exact IH.
      * simpl. rewrite Hlegacy. exact IH.
Qed.

Lemma legacy_utxo_count_remove_inputs_le : forall ins U,
  legacy_utxo_count (remove_inputs U ins) <= legacy_utxo_count U.
Proof.
  induction ins as [| inp rest IH]; intros U; simpl.
  - lia.
  - eapply Nat.le_trans.
    + apply IH.
    + apply legacy_utxo_count_remove_le.
Qed.

Lemma legacy_utxo_count_app_single : forall U k out,
  legacy_utxo_count (U ++ [(k, out)]) =
  legacy_utxo_count U + (if output_is_legacy out then 1 else 0).
Proof.
  induction U as [| [k' out'] rest IH]; intros k out; simpl.
  - destruct (output_is_legacy out); lia.
  - rewrite IH.
    destruct (output_is_legacy out'); destruct (output_is_legacy out); lia.
Qed.

Lemma legacy_utxo_count_add_outputs : forall outs U base,
  legacy_utxo_count (add_outputs U outs base) =
  legacy_utxo_count U + legacy_tx_output_count outs.
Proof.
  induction outs as [| out rest IH]; intros U base; simpl.
  - lia.
  - rewrite IH.
    rewrite legacy_utxo_count_app_single.
    unfold output_is_legacy, tx_output_is_legacy, is_legacy_script_version.
    simpl. lia.
Qed.

Theorem delta_tx_legacy_count_nonincreasing_after_announcement :
  forall U tx height config fresh_id,
    valid_tx_structural U tx height config = true ->
    announcement_height config <= height ->
    legacy_utxo_count (delta_tx U tx fresh_id) <= legacy_utxo_count U.
Proof.
  intros U tx height config fresh_id Hvalid Hannounced.
  unfold delta_tx.
  rewrite legacy_utxo_count_add_outputs.
  rewrite (valid_tx_structural_no_legacy_outputs_after_announcement U tx height config Hvalid Hannounced).
  pose proof (legacy_utxo_count_remove_inputs_le (inputs tx) U) as Hremove.
  lia.
Qed.

Theorem apply_block_transitions_structural_legacy_count_nonincreasing_after_announcement :
  forall U txs height config fresh_id U',
    announcement_height config <= height ->
    apply_block_transitions_structural U txs height config fresh_id = Some U' ->
    legacy_utxo_count U' <= legacy_utxo_count U.
Proof.
  intros U txs. revert U.
  induction txs as [| tx rest IH]; intros U height config fresh_id U' Hannounced Happly; simpl in *.
  - inversion Happly. lia.
  - destruct (valid_tx_structural U tx height config) eqn:Hvalid; try discriminate.
    pose proof
      (delta_tx_legacy_count_nonincreasing_after_announcement
        U tx height config fresh_id Hvalid Hannounced)
      as Hdelta.
    specialize
      (IH
        (delta_tx U tx fresh_id)
        height
        config
        (fresh_id + length (outputs tx))
        U'
        Hannounced
        Happly).
    lia.
Qed.

Theorem apply_valid_block_structural_legacy_count_nonincreasing_after_announcement :
  forall U txs height config fresh_id U',
    announcement_height config <= height ->
    apply_valid_block_structural U txs height config fresh_id = Some U' ->
    legacy_utxo_count U' <= legacy_utxo_count U.
Proof.
  intros U txs height config fresh_id U' Hannounced Happly.
  unfold apply_valid_block_structural in Happly.
  destruct (apply_block_transitions_structural U txs height config fresh_id)
    as [U_trans |] eqn:Htransitions; try discriminate.
  destruct (check_block_cost_structural txs) eqn:Hcost; try discriminate.
  inversion Happly. subst U_trans.
  eapply apply_block_transitions_structural_legacy_count_nonincreasing_after_announcement; eauto.
Qed.

Theorem apply_valid_block_structural_frozen_count_nonincreasing_after_cutover :
  forall U txs height config fresh_id U',
    announcement_height config <= cutover_height config ->
    cutover_height config <= height ->
    apply_valid_block_structural U txs height config fresh_id = Some U' ->
    frozen_utxo_count height config U' <= frozen_utxo_count height config U.
Proof.
  intros U txs height config fresh_id U' Hconfig_order Hcutover Happly.
  unfold frozen_utxo_count.
  assert (Hpost_cutover : (height <? cutover_height config) = false).
  { apply Nat.ltb_ge. exact Hcutover. }
  rewrite Hpost_cutover.
  eapply apply_valid_block_structural_legacy_count_nonincreasing_after_announcement.
  - eapply Nat.le_trans.
    + exact Hconfig_order.
    + exact Hcutover.
  - exact Happly.
Qed.

Theorem valid_block_structural_deterministic :
  forall U txs height config fresh_id,
    valid_block_structural U txs height config fresh_id =
    valid_block_structural U txs height config fresh_id.
Proof.
  reflexivity.
Qed.

Theorem apply_block_transitions_structural_equiv :
  forall U txs height config fresh_id,
    option_is_some
      (apply_block_transitions_structural U txs height config fresh_id) =
    valid_block_transitions_structural U txs height config fresh_id.
Proof.
  intros U txs. revert U.
  induction txs as [| tx rest IH]; intros U height config fresh_id; simpl.
  - reflexivity.
  - destruct (valid_tx_structural U tx height config) eqn:Hvalid.
    + apply IH.
    + reflexivity.
Qed.

Theorem apply_valid_block_structural_equiv :
  forall U txs height config fresh_id,
    option_is_some (apply_valid_block_structural U txs height config fresh_id) =
    valid_block_structural U txs height config fresh_id.
Proof.
  intros U txs height config fresh_id.
  pose proof
    (apply_block_transitions_structural_equiv U txs height config fresh_id)
    as Htransitions.
  unfold apply_valid_block_structural, valid_block_structural.
  destruct (apply_block_transitions_structural U txs height config fresh_id)
    as [U' |] eqn:Happly; simpl.
  - simpl in Htransitions. rewrite <- Htransitions.
    destruct (check_block_cost_structural txs); reflexivity.
  - simpl in Htransitions. rewrite <- Htransitions. reflexivity.
Qed.

Lemma option_is_some_exists :
  forall (A : Type) (value : option A),
    option_is_some value = true <-> exists result, value = Some result.
Proof.
  intros A value. destruct value as [result |]; simpl.
  - split.
    + intros _. exists result. reflexivity.
    + intros _. reflexivity.
  - split.
    + discriminate.
    + intros [result H]. discriminate.
Qed.

Theorem apply_valid_block_structural_some_iff_valid :
  forall U txs height config fresh_id,
    (exists U',
      apply_valid_block_structural U txs height config fresh_id = Some U') <->
    valid_block_structural U txs height config fresh_id = true.
Proof.
  intros U txs height config fresh_id.
  rewrite <- apply_valid_block_structural_equiv.
  symmetry. apply option_is_some_exists.
Qed.

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

    PO-6: Invariant Preservation
    4. [apply_valid_block_structural_preserves_domain_nodup]:
       valid structural block application preserves a unique UTXO domain
       under the explicit fresh-id bound
    5. [apply_valid_block_structural_preserves_total_value]:
       valid structural block application cannot increase total UTXO value
       under the same duplicate-free domain and fresh-id bound
    6. [apply_valid_block_structural_legacy_count_nonincreasing_after_announcement]:
       accepted structural block application cannot increase the number of
       legacy outputs after the migration announcement height
    7. [apply_valid_block_structural_inputs_pq_after_cutover]:
       accepted structural block application after cutover consumes only PQ
       present inputs, matching the freeze predicate boundary
    8. [apply_valid_block_structural_frozen_count_nonincreasing_after_cutover]:
       under the valid migration-height ordering, accepted structural block
       application after cutover cannot increase frozen legacy UTXOs

    PO-7: Cost Boundedness
    9. [cost_bounded_by_weight]: Cost(tx) ≤ 1 · weight(tx)
    10. [cost_equals_weight]: Cost(tx) = weight(tx) (exact equality)
    11. [block_cost_bounded_by_weights]: block invariant implies per-tx bound

    Correspondence to other artifacts:
    - UTXO model matches [formal/tla/BitcoinPQ.tla] (outpoint ids, delta)
    - Cost constants match [src/weight.rs] (144, 40, 164, 4)
    - Block cost invariant matches [src/params.rs] (C_MAX = 4,000,000)
*)
