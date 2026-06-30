(* ExtractTxidVectors: OCaml extraction driver for txid preimage vectors. *)

From Coq Require Import Extraction.
From BitcoinPQ.extraction Require Import TxidExtraction.

Extraction Language OCaml.

Extraction "txid_extracted.ml"
  TxidExtraction.extract_txid_preimage_domain
  TxidExtraction.extract_serialize_txid_input
  TxidExtraction.extract_serialize_txid_outputs
  TxidExtraction.extract_txid_preimage.
