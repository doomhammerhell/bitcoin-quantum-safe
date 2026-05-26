(* SighashExtraction: extraction-facing wrappers for PO-4 transcript refinement.
 *
 * The Coq model intentionally axiomatizes SHA-256. These wrappers therefore
 * expose the deterministic serialization boundary around SHA-256 rather than
 * attempting to compute the cryptographic primitive inside Coq.
 *)

From Coq Require Import Extraction.
From BitcoinPQ Require Import SighashV2.

(* Use the same native extraction profile as the witness refinement harness. *)
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
Extract Constant nat_to_le4 =>
  "(fun n -> [n land 0xff; (n lsr 8) land 0xff; (n lsr 16) land 0xff; (n lsr 24) land 0xff])".
Extract Constant nat_to_le8 =>
  "(fun n -> [n land 0xff; (n lsr 8) land 0xff; (n lsr 16) land 0xff; (n lsr 24) land 0xff; (n lsr 32) land 0xff; (n lsr 40) land 0xff; (n lsr 48) land 0xff; (n lsr 56) land 0xff])".

Module SighashExtraction.

Definition extract_nat_to_le4 := nat_to_le4.
Definition extract_nat_to_le8 := nat_to_le8.
Definition extract_serialize_outpoint := serialize_outpoint.
Definition extract_serialize_output := serialize_output.
Definition extract_serialize_spent_output := serialize_spent_output.
Definition extract_sighash_preimage_from_hashes := sighash_preimage_from_hashes.

End SighashExtraction.
