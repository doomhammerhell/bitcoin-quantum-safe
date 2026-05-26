(* ExtractSighashVectors: OCaml extraction driver for PO-4 transcript vectors.
 *
 * The extracted functions cover deterministic sighash transcript serialization:
 * fixed-width little-endian integers, outpoint/output/spent-output
 * serialization, and final preimage assembly with supplied 32-byte sub-hashes.
 *)

From Coq Require Import Extraction.
From BitcoinPQ.extraction Require Import SighashExtraction.

Extraction Language OCaml.

Extraction "sighash_extracted.ml"
  SighashExtraction.extract_nat_to_le4
  SighashExtraction.extract_nat_to_le8
  SighashExtraction.extract_serialize_outpoint
  SighashExtraction.extract_serialize_output
  SighashExtraction.extract_serialize_spent_output
  SighashExtraction.extract_sighash_preimage_from_hashes.
