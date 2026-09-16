(* ExtractPQProfileVectors: OCaml extraction driver for PQ profile refinement. *)

From Coq Require Import Extraction.
From BitcoinPQ.extraction Require Import PQProfileExtraction.

Extraction Language OCaml.

Extraction "pq_profile_extracted.ml"
  PQProfileExtraction.extract_profile_rows
  PQProfileExtraction.extract_primary_scheme_code
  PQProfileExtraction.extract_fallback_scheme_code
  PQProfileExtraction.extract_implemented_scheme_codes
  PQProfileExtraction.extract_consensus_enabled_scheme_codes
  PQProfileExtraction.extract_standards_distinct
  PQProfileExtraction.extract_assumptions_distinct
  PQProfileExtraction.extract_all_profiles_fit_cap
  PQProfileExtraction.extract_consensus_enabled_exactly_primary
  PQProfileExtraction.extract_active_suite_standards_aligned.
