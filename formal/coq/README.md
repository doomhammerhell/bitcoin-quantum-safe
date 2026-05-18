# Coq Mechanization

Machine-checked and executable-evidence artifacts for the PQ witness protocol.
The core checked proofs currently cover PO-1, PO-2, PO-3, PO-4, PO-5, PO-7, and
the bounded varint/canonical witness discharge used for PO-8 evidence. PO-4 is
proved for the Coq sighash model under the SHA-256 collision-resistance axiom.
Rust property-based tests, Kani source-level bounded harnesses, and release
binary translation validation provide executable implementation evidence for the
concrete code; a proof of compiler correctness remains outside the current proof
boundary.

The repository-level proof-status ledger is
[`../../PROOF_OBLIGATIONS.md`](../../PROOF_OBLIGATIONS.md).

## Verified Properties

### PO-1, PO-2, PO-3: Spend Predicate Core

| Theorem | PO | Property |
|---|---|---|
| `spend_pred_pq_total` | PO-1 | Totality: predicate always returns true or false |
| `spend_pred_pq_deterministic` | PO-2 | Determinism: same inputs, same output |
| `spend_pred_pq_deterministic_ext` | PO-2 | Extensional determinism |
| `parse_varint_extracts` | PO-3 | Parse decomposes witness into (pk, sig) |
| `parse_canonical` | PO-3 | Parse output determines witness content |
| `spend_pred_pq_iff` | — | Complete characterization of acceptance |
| `spend_pred_pq_none_is_false` | — | Parse failure implies rejection |
| `spend_pred_pq_hash_mismatch` | — | Hash mismatch implies rejection |
| `spend_pred_pq_vfy_fail` | — | Verification failure implies rejection |

### PO-4: Sighash Commitment (SighashV2.v) — Verified Model

| Theorem | Status | Property |
|---|---|---|
| `sha256_collision_resistance` | Axiom | Equal SHA-256 outputs imply equal inputs in the model |
| `nat_to_le4_reconstruct`, `nat_to_le4_injective` | Verified | 4-byte little-endian reconstruction and injectivity under u32 bounds |
| `nat_to_le8_reconstruct`, `nat_to_le8_injective` | Verified | 8-byte little-endian reconstruction and injectivity under u64 bounds |
| `app_last_4_eq` | Verified | Proved from list split injectivity plus `nat_to_le4_injective` |
| `serialize_outpoint_injective` | Verified | Proved for `wf_outpoint` values |
| `serialize_output_injective`, `serialize_spent_output_injective` | Verified | Proved for fixed-width transaction/spent outputs |
| `concat_input_outpoints_injective`, `concat_outputs_injective` | Verified | Proved for concatenated fixed-width serializations |
| `hash_outpoints_injective`, `hash_outputs_injective` | Verified under hash axiom | Derived from `tagged_hash_injective` and fixed-width serialization |
| `wf_transaction`, `wf_spent_output` | Definitions | Scope PO-4 claims to fixed-width consensus fields |
| `sighash_v2_injective` | Verified under hash axiom | For well-formed inputs and u32 input indices, equal sighashes imply equal consensus-significant fields, input outpoints, input index, and spent output |
| `sighash_cross_input_separation` | Verified under hash axiom | Derived from `sighash_v2_injective` |
| `sighash_field_coverage_input_outpoints`, `sighash_field_coverage_outputs` | Verified under hash axiom | Derived from `sighash_v2_injective`; cover transaction input outpoints and outputs |
| `sighash_field_coverage_version`, `sighash_field_coverage_locktime` | Verified under hash axiom | Derived from `sighash_v2_injective`; cover transaction scalar fields |
| `sighash_field_coverage_spent_*` | Verified under hash axiom | Derived from `sighash_v2_injective`; cover spent output script version, commitment, and value |
| `sighash_v2_commitment_property` | Verified record | Assembles the PO-4 theorem shape |

This file proves the Coq sighash model, not a full refinement theorem for the
concrete Rust implementation. The concrete implementation is covered by Rust
property-based tests for injectivity, cross-input separation, field coverage,
and tagged-hash domain separation.

### PO-5 and PO-7: UTXO Transitions and Cost Model

| Theorem | PO | Property |
|---|---|---|
| `delta_tx_deterministic_ext` | PO-5 | Transition determinism |
| `delta_tx_preserves_no_double_spend` | PO-5 | No-double-spend preservation |
| `cost_bounded_by_weight` | PO-7 | Cost bounded by transaction weight |
| `cost_equals_weight` | PO-7 | Exact equality for the modeled weight function |
| `block_cost_bounded_by_weights` | PO-7 | Block-level cost bound |

### PO-8: Implementation Correspondence — Bounded Extraction + Source/Compiled Evidence

| Component | Status |
|---|---|
| Varint axiom discharge | Proven for `0..=65535` |
| Concrete witness canonicality | `parse_witness_concrete_determines_serialize` proves every accepted concrete witness is exactly canonical |
| Concrete parse injectivity | `parse_witness_concrete_injective` |
| Exhaustive varint refinement | Coq-extracted `encode_len_multi`/`decode_len_multi` and Rust `encode_varint`/`decode_varint` agree over all `0..=65535` values plus canonical rejection cases |
| Witness-level refinement | Coq-extracted `serialize_witness_concrete`/`parse_witness_concrete`/consensus-domain parse/canonicality/operational-trace behavior matches Rust `serialize_witness`/`parse_witness`/`parse_consensus_witness`/`parse_witness_trace`/`is_canonical_witness`/`is_canonical_consensus_witness` over the deterministic boundary/rejection matrix plus 111,111 symbolic bounded witnesses |
| Witness serializer extraction | Generated by `extraction/ExtractWitnessVectors.v` |
| Golden test vectors | 7 bounded vectors: single-byte and `0xFD/u16` cases |
| Byte-for-byte verification | Coq-extracted serializer harness matches Rust generator |
| Consensus witness-size guard | `max_witness_size = 16000 <= max_u16`, plus parsed/serialized component length and bounded-canonicality theorems |
| Consensus parser theorem | `parse_consensus_witness_concrete_*` proves that the consensus-domain parser equals the byte-level parser below the cap, rejects above the cap, and only accepts canonical modeled-domain witnesses |
| Source-level Rust refinement | 5 Kani harnesses in `../../src/kani_proofs.rs` prove bounded symbolic alignment between the Rust layout parser, public parser, consensus parser, trace hook, canonicality predicates, and oversize guard |
| Compiled-artifact translation validation | `../../verify_compiled_refinement.sh` builds release examples, compares their outputs against Coq-extracted summaries, and emits a source/binary hash certificate |
| Full CompactSize coverage | Rust implements/tests `0xFE` and `0xFF`; not yet modeled in Coq |
| Compiler correctness | Not proved |

See `extraction/README.md` for the vector provenance and formal boundary.

## Build

Requires Rocq/Coq 9.x (or Coq 8.18+).

```sh
make        # compile all proofs
make clean  # remove artifacts
```

## Design

The cryptographic primitives (`H`, `Vfy`) are axiomatized as parameters, matching the paper's approach: security theorems hold for any PQC-Sig satisfying EUF-CMA. The witness encoding uses `pk_len || pk || sig_len || sig`. All functions are pure (no state, no randomness, no IO), so totality and determinism follow from Coq's type system, but we state them as explicit theorems for correspondence with the paper's proof obligations.

## Remaining Obligations

- If full compiler-level PO-8 closure is required, prove compiler correctness or
  replace the current implementation path with a verified compiler/translation
  chain. The current Coq side proves bounded concrete parse/serialize
  canonicality and injectivity, CI exhaustively checks the Coq-extracted varint
  encoder/decoder against Rust over `0..=65535`, CI compares extracted witness
  serialize/parse/canonicality behavior, consensus-domain parse/canonicality
  behavior, and parser decision traces against Rust over a deterministic
  boundary/rejection matrix and a symbolic bounded state-space over critical
  modeled-domain bytes, CI runs Kani source-level bounded harnesses over the Rust
  parser implementation, and CI validates release binaries against the same
  Coq-extracted summaries. The remaining gap is no longer witness-level
  executable refinement, bounded source-level parser proof, or compiled-artifact
  validation; it is compiler correctness.
  Extending
  `VarintConcrete.v` to `0xFE`/`0xFF` remains necessary only if the project
  claims general-purpose CompactSize verification or raises the witness cap
  above `65535`.
- Connect the finite TLA+ PO-6 model to the Coq/Rust transition artifacts if the
  project requires a single cross-artifact proof ledger.

## Technical Debt

- Generated extraction files (`golden_vectors_extracted.ml`, `.mli`, `.cmi`,
  `.cmo`, and the `golden_vectors` binary) are build artifacts and should not be
  versioned.
- The stale, incomplete `TestSighash.v` duplicate was removed. `SighashV2.v` is
  the canonical PO-4 Coq artifact.
