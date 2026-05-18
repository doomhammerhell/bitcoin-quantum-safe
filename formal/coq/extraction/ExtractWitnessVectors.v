(* ExtractWitnessVectors: OCaml extraction driver for PO-8 vector generation.
 *
 * This file is intentionally separate from WitnessExtraction.v so CI can
 * produce golden_vectors_extracted.ml via coqc rather than relying on coqtop
 * stdin behavior. The JSON harness remains handwritten OCaml, but witness
 * bytes are produced by the extracted serializer below.
 *)

From Coq Require Import Extraction.
From BitcoinPQ.extraction Require Import WitnessExtraction.

Extraction Language OCaml.

Extraction "golden_vectors_extracted.ml"
  WitnessExtraction.extract_encode_varint
  WitnessExtraction.extract_decode_varint
  WitnessExtraction.extract_serialize_witness
  WitnessExtraction.extract_parse_witness
  WitnessExtraction.extract_parse_consensus_witness
  WitnessExtraction.extract_is_canonical_witness
  WitnessExtraction.extract_is_canonical_witness_bytes
  WitnessExtraction.extract_is_canonical_consensus_witness_bytes
  WitnessExtraction.extract_parse_witness_trace.
