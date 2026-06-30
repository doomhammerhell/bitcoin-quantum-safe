(* TxidExtraction: extraction-facing wrappers for txid preimage refinement.
 *
 * This module exposes the deterministic txid transcript from TxidPreimage.v.
 * The boundary is deliberately pre-hash: SHA-256 collision resistance and
 * implementation correctness remain outside the Coq extraction artifact.
 *)

From Coq Require Import Extraction.
From BitcoinPQ Require Import SighashV2 TxidPreimage.

(* Native extraction profile shared with the other refinement harnesses. *)
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
Extract Inlined Constant Nat.div => "( / )".
Extract Inlined Constant Nat.modulo => "( mod )".
Extract Constant pow2_8 => "256".
Extract Constant pow2_16 => "65536".
Extract Constant pow2_24 => "16777216".
Extract Constant pow2_32 => "4294967296".
Extract Constant pow2_64 => "18446744073709551616".
Extract Constant nat_to_le4 =>
  "(fun n -> [n land 0xff; (n lsr 8) land 0xff; (n lsr 16) land 0xff; (n lsr 24) land 0xff])".
Extract Constant nat_to_le8 =>
  "(fun n -> [n land 0xff; (n lsr 8) land 0xff; (n lsr 16) land 0xff; (n lsr 24) land 0xff; (n lsr 32) land 0xff; (n lsr 40) land 0xff; (n lsr 48) land 0xff; (n lsr 56) land 0xff])".

Module TxidExtraction.

Definition extract_txid_preimage_domain := TXID_PREIMAGE_DOMAIN.
Definition extract_serialize_txid_input := serialize_txid_input.
Definition extract_serialize_txid_outputs := serialize_txid_outputs.
Definition extract_txid_preimage := txid_preimage.

End TxidExtraction.
