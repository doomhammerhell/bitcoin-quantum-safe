(** * TxidPreimage: Mechanized txid transcript model
 *
 * Copyright (c) 2026 Mayckon Giovani. MIT License.
 *
 * This module formalizes the Rust `txid_preimage` transcript used by
 * `compute_txid`. The transaction id deliberately excludes witness bytes, so
 * the injectivity theorem is stated over the committed txid shape:
 *
 *   version, input outpoints, outputs, locktime.
 *
 * This is the exact structural boundary hashed by SHA-256 in Rust. SHA-256
 * itself remains outside this module; PO-5/txid refinement compares the
 * extracted preimage bytes against the Rust implementation.
 *)

From Coq Require Import List.
From Coq Require Import Lia.

From BitcoinPQ Require Import SighashV2.

Import ListNotations.

(* ASCII bytes for "BitcoinPQ:txid:v1". *)
Definition TXID_PREIMAGE_DOMAIN : list nat :=
  [66; 105; 116; 99; 111; 105; 110; 80; 81; 58; 116; 120; 105; 100; 58; 118; 49].

Definition serialize_txid_input (txi : TxInput) : list nat :=
  serialize_outpoint txi.(txi_outpoint).

Definition serialize_txid_inputs (inputs : list TxInput) : list nat :=
  concat (map serialize_txid_input inputs).

Definition serialize_txid_outputs (outputs : list TxOutput) : list nat :=
  concat (map serialize_output outputs).

Definition txid_preimage (tx : Transaction) : list nat :=
  TXID_PREIMAGE_DOMAIN ++
  nat_to_le4 tx.(tx_version) ++
  nat_to_le8 (length tx.(tx_inputs)) ++
  serialize_txid_inputs tx.(tx_inputs) ++
  nat_to_le8 (length tx.(tx_outputs)) ++
  serialize_txid_outputs tx.(tx_outputs) ++
  nat_to_le4 tx.(tx_locktime).

(** The projection committed by `txid_preimage`. Witness bytes are intentionally
    absent, matching Bitcoin-style txid semantics and the Rust implementation. *)
Record TxidShape : Type := mkTxidShape {
  shape_version : nat;
  shape_input_outpoints : list OutPoint;
  shape_outputs : list TxOutput;
  shape_locktime : nat
}.

Definition txid_shape (tx : Transaction) : TxidShape :=
  mkTxidShape
    tx.(tx_version)
    (tx_input_outpoints tx)
    tx.(tx_outputs)
    tx.(tx_locktime).

Lemma serialize_txid_input_length : forall txi,
  wf_tx_input txi ->
  length (serialize_txid_input txi) = 36.
Proof.
  intros txi Hwf.
  unfold serialize_txid_input.
  apply serialize_outpoint_length.
  exact Hwf.
Qed.

Lemma serialize_txid_inputs_length : forall inputs,
  Forall wf_tx_input inputs ->
  length (serialize_txid_inputs inputs) = 36 * length inputs.
Proof.
  intros inputs Hwf.
  induction Hwf as [|input inputs Hinput Hinputs IH].
  - reflexivity.
  - unfold serialize_txid_inputs in *.
    cbn [map concat length].
    rewrite app_length.
    rewrite serialize_txid_input_length by exact Hinput.
    rewrite IH.
    lia.
Qed.

Lemma serialize_txid_outputs_length : forall outputs,
  Forall wf_tx_output outputs ->
  length (serialize_txid_outputs outputs) = 41 * length outputs.
Proof.
  intros outputs Hwf.
  induction Hwf as [|output outputs Houtput Houtputs IH].
  - reflexivity.
  - unfold serialize_txid_outputs in *.
    cbn [map concat length].
    rewrite app_length.
    rewrite serialize_output_length by exact Houtput.
    rewrite IH.
    lia.
Qed.

Lemma serialize_txid_inputs_injective : forall inputs1 inputs2,
  Forall wf_tx_input inputs1 ->
  Forall wf_tx_input inputs2 ->
  serialize_txid_inputs inputs1 = serialize_txid_inputs inputs2 ->
  tx_input_outpoints (mkTransaction 0 inputs1 [] 0) =
  tx_input_outpoints (mkTransaction 0 inputs2 [] 0).
Proof.
  intros inputs1 inputs2 Hwf1 Hwf2 Hser.
  unfold serialize_txid_inputs in Hser.
  unfold serialize_txid_input in Hser.
  unfold tx_input_outpoints.
  simpl.
  eapply concat_input_outpoints_injective; eauto.
Qed.

Lemma serialize_txid_outputs_injective : forall outputs1 outputs2,
  Forall wf_tx_output outputs1 ->
  Forall wf_tx_output outputs2 ->
  serialize_txid_outputs outputs1 = serialize_txid_outputs outputs2 ->
  outputs1 = outputs2.
Proof.
  intros outputs1 outputs2 Hwf1 Hwf2 Hser.
  unfold serialize_txid_outputs in Hser.
  eapply concat_outputs_injective; eauto.
Qed.

(** `txid_preimage` is structurally injective over the committed txid shape.

    It cannot be injective over full `Transaction` values because witness bytes
    are intentionally excluded from txid computation. The theorem therefore
    proves exactly the field commitment provided by the transcript. *)
Theorem txid_preimage_injective : forall tx1 tx2,
  wf_transaction tx1 ->
  wf_transaction tx2 ->
  length tx1.(tx_inputs) < pow2_64 ->
  length tx2.(tx_inputs) < pow2_64 ->
  length tx1.(tx_outputs) < pow2_64 ->
  length tx2.(tx_outputs) < pow2_64 ->
  txid_preimage tx1 = txid_preimage tx2 ->
  txid_shape tx1 = txid_shape tx2.
Proof.
  intros tx1 tx2 Hwf1 Hwf2 Hinputs_bound1 Hinputs_bound2
    Houtputs_bound1 Houtputs_bound2 Hpreimage.
  destruct Hwf1 as [Hversion1 [Hinputs1 [Houtputs1 Hlocktime1]]].
  destruct Hwf2 as [Hversion2 [Hinputs2 [Houtputs2 Hlocktime2]]].
  unfold txid_preimage in Hpreimage.

  pose proof (app_inj_tail nat TXID_PREIMAGE_DOMAIN TXID_PREIMAGE_DOMAIN
    (nat_to_le4 tx1.(tx_version) ++
     nat_to_le8 (length tx1.(tx_inputs)) ++
     serialize_txid_inputs tx1.(tx_inputs) ++
     nat_to_le8 (length tx1.(tx_outputs)) ++
     serialize_txid_outputs tx1.(tx_outputs) ++
     nat_to_le4 tx1.(tx_locktime))
    (nat_to_le4 tx2.(tx_version) ++
     nat_to_le8 (length tx2.(tx_inputs)) ++
     serialize_txid_inputs tx2.(tx_inputs) ++
     nat_to_le8 (length tx2.(tx_outputs)) ++
     serialize_txid_outputs tx2.(tx_outputs) ++
     nat_to_le4 tx2.(tx_locktime))
    eq_refl Hpreimage) as [_ Hafter_domain].

  assert (Hversion_len :
    length (nat_to_le4 tx1.(tx_version)) =
    length (nat_to_le4 tx2.(tx_version))).
  { repeat rewrite nat_to_le4_length. reflexivity. }
  pose proof (app_inj_tail nat
    (nat_to_le4 tx1.(tx_version))
    (nat_to_le4 tx2.(tx_version))
    (nat_to_le8 (length tx1.(tx_inputs)) ++
     serialize_txid_inputs tx1.(tx_inputs) ++
     nat_to_le8 (length tx1.(tx_outputs)) ++
     serialize_txid_outputs tx1.(tx_outputs) ++
     nat_to_le4 tx1.(tx_locktime))
    (nat_to_le8 (length tx2.(tx_inputs)) ++
     serialize_txid_inputs tx2.(tx_inputs) ++
     nat_to_le8 (length tx2.(tx_outputs)) ++
     serialize_txid_outputs tx2.(tx_outputs) ++
     nat_to_le4 tx2.(tx_locktime))
    Hversion_len Hafter_domain) as [Hversion_bytes Hafter_version].
  assert (Hversion : tx1.(tx_version) = tx2.(tx_version)).
  {
    apply (nat_to_le4_injective tx1.(tx_version) tx2.(tx_version));
      assumption.
  }

  assert (Hinput_count_len :
    length (nat_to_le8 (length tx1.(tx_inputs))) =
    length (nat_to_le8 (length tx2.(tx_inputs)))).
  { repeat rewrite nat_to_le8_length. reflexivity. }
  pose proof (app_inj_tail nat
    (nat_to_le8 (length tx1.(tx_inputs)))
    (nat_to_le8 (length tx2.(tx_inputs)))
    (serialize_txid_inputs tx1.(tx_inputs) ++
     nat_to_le8 (length tx1.(tx_outputs)) ++
     serialize_txid_outputs tx1.(tx_outputs) ++
     nat_to_le4 tx1.(tx_locktime))
    (serialize_txid_inputs tx2.(tx_inputs) ++
     nat_to_le8 (length tx2.(tx_outputs)) ++
     serialize_txid_outputs tx2.(tx_outputs) ++
     nat_to_le4 tx2.(tx_locktime))
    Hinput_count_len Hafter_version) as [Hinput_count_bytes Hafter_input_count].
  assert (Hinput_count : length tx1.(tx_inputs) = length tx2.(tx_inputs)).
  {
    apply (nat_to_le8_injective (length tx1.(tx_inputs)) (length tx2.(tx_inputs)));
      assumption.
  }

  pose proof (serialize_txid_inputs_length tx1.(tx_inputs) Hinputs1) as Hinputs_len1.
  pose proof (serialize_txid_inputs_length tx2.(tx_inputs) Hinputs2) as Hinputs_len2.
  assert (Hserialized_inputs_len :
    length (serialize_txid_inputs tx1.(tx_inputs)) =
    length (serialize_txid_inputs tx2.(tx_inputs))) by lia.
  pose proof (app_inj_tail nat
    (serialize_txid_inputs tx1.(tx_inputs))
    (serialize_txid_inputs tx2.(tx_inputs))
    (nat_to_le8 (length tx1.(tx_outputs)) ++
     serialize_txid_outputs tx1.(tx_outputs) ++
     nat_to_le4 tx1.(tx_locktime))
    (nat_to_le8 (length tx2.(tx_outputs)) ++
     serialize_txid_outputs tx2.(tx_outputs) ++
     nat_to_le4 tx2.(tx_locktime))
    Hserialized_inputs_len Hafter_input_count) as [Hinputs_bytes Hafter_inputs].
  assert (Hinput_outpoints :
    tx_input_outpoints tx1 = tx_input_outpoints tx2).
  { unfold tx_input_outpoints.
    change (map (fun inp : TxInput => txi_outpoint inp) (tx_inputs tx1) =
            map (fun inp : TxInput => txi_outpoint inp) (tx_inputs tx2)).
    unfold serialize_txid_inputs, serialize_txid_input in Hinputs_bytes.
    apply (concat_input_outpoints_injective tx1.(tx_inputs) tx2.(tx_inputs));
      assumption. }

  assert (Houtput_count_len :
    length (nat_to_le8 (length tx1.(tx_outputs))) =
    length (nat_to_le8 (length tx2.(tx_outputs)))).
  { repeat rewrite nat_to_le8_length. reflexivity. }
  pose proof (app_inj_tail nat
    (nat_to_le8 (length tx1.(tx_outputs)))
    (nat_to_le8 (length tx2.(tx_outputs)))
    (serialize_txid_outputs tx1.(tx_outputs) ++ nat_to_le4 tx1.(tx_locktime))
    (serialize_txid_outputs tx2.(tx_outputs) ++ nat_to_le4 tx2.(tx_locktime))
    Houtput_count_len Hafter_inputs) as [Houtput_count_bytes Hafter_output_count].
  assert (Houtput_count : length tx1.(tx_outputs) = length tx2.(tx_outputs)).
  {
    apply (nat_to_le8_injective (length tx1.(tx_outputs)) (length tx2.(tx_outputs)));
      assumption.
  }

  pose proof (serialize_txid_outputs_length tx1.(tx_outputs) Houtputs1) as Houtputs_len1.
  pose proof (serialize_txid_outputs_length tx2.(tx_outputs) Houtputs2) as Houtputs_len2.
  assert (Hserialized_outputs_len :
    length (serialize_txid_outputs tx1.(tx_outputs)) =
    length (serialize_txid_outputs tx2.(tx_outputs))) by lia.
  pose proof (app_inj_tail nat
    (serialize_txid_outputs tx1.(tx_outputs))
    (serialize_txid_outputs tx2.(tx_outputs))
    (nat_to_le4 tx1.(tx_locktime))
    (nat_to_le4 tx2.(tx_locktime))
    Hserialized_outputs_len Hafter_output_count) as [Houtputs_bytes Hlocktime_bytes].
  assert (Houtputs : tx1.(tx_outputs) = tx2.(tx_outputs)).
  {
    apply (serialize_txid_outputs_injective tx1.(tx_outputs) tx2.(tx_outputs));
      assumption.
  }
  assert (Hlocktime : tx1.(tx_locktime) = tx2.(tx_locktime)).
  {
    apply (nat_to_le4_injective tx1.(tx_locktime) tx2.(tx_locktime));
      assumption.
  }

  unfold txid_shape.
  rewrite Hversion.
  rewrite Hinput_outpoints.
  rewrite Houtputs.
  rewrite Hlocktime.
  reflexivity.
Qed.
