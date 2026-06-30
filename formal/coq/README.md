# Coq Mechanization

Machine-checked and executable-evidence artifacts for the PQ witness protocol.
The core checked proofs currently cover PO-1, PO-2, PO-3, PO-4, PO-5, PO-7, and
the bounded varint/canonical witness discharge used for PO-8 evidence. PO-4 is
proved for the Coq sighash model under the SHA-256 collision-resistance axiom
and now includes a Coq-extracted transcript constructor compared against the
Rust preimage serialization path. PO-5 now includes a mechanized
`txid_preimage` transcript with structural injectivity over the committed
txid shape, Coq-extracted txid/transition summaries compared against Rust
transaction/block transition functions, plus Kani bounded source-level
harnesses for deployed `valid_tx`, `delta_tx`, and `valid_block` transition
behavior. The runtime layer also validates txid preimage/hash wiring and
UTXO-store extensional behavior against independent deterministic references.
Rust property-based tests, Kani
source-level bounded harnesses, and release-binary validation provide executable
implementation evidence for the concrete code; proofs of SHA-256 primitive
correctness, unbounded source-level transition refinement, and compiler
correctness remain outside the current proof boundary.

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

### PO-4: Sighash Commitment (SighashV2.v) — Verified Model + Transcript Refinement

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
| `sighash_preimage_from_hashes` | Extracted structural function | Final preimage assembly with supplied 32-byte sub-hashes, separating deterministic transcript construction from SHA-256 |
| `sighash_preimage_from_hashes_agrees` | Verified | The extracted transcript function agrees with the modeled `sighash_preimage` when supplied with modeled sub-hashes |
| `wf_transaction`, `wf_spent_output` | Definitions | Scope PO-4 claims to fixed-width consensus fields |
| `sighash_v2_injective` | Verified under hash axiom | For well-formed inputs and u32 input indices, equal sighashes imply equal consensus-significant fields, input outpoints, input index, and spent output |
| `sighash_cross_input_separation` | Verified under hash axiom | Derived from `sighash_v2_injective` |
| `sighash_field_coverage_input_outpoints`, `sighash_field_coverage_outputs` | Verified under hash axiom | Derived from `sighash_v2_injective`; cover transaction input outpoints and outputs |
| `sighash_field_coverage_version`, `sighash_field_coverage_locktime` | Verified under hash axiom | Derived from `sighash_v2_injective`; cover transaction scalar fields |
| `sighash_field_coverage_spent_*` | Verified under hash axiom | Derived from `sighash_v2_injective`; cover spent output script version, commitment, and value |
| `sighash_v2_commitment_property` | Verified record | Assembles the PO-4 theorem shape |

This file proves the Coq sighash model and exposes the deterministic final
preimage assembly for extraction. `extraction/SighashExtraction.v` and
`extraction/sighash_refinement.ml` compare the extracted transcript summary
against the Rust functions in `../../src/sighash.rs`, including outpoint
serialization, output serialization, spent-output serialization, and final
preimage assembly with supplied sub-hashes. The concrete implementation is also
covered by Rust property-based tests for injectivity, cross-input separation,
field coverage, and tagged-hash domain separation. The remaining PO-4 boundary
is the SHA-256 primitive/axiom and compiler/toolchain correctness, not the
modeled transcript layout.

### PO-5 and PO-7: UTXO Transitions and Cost Model

| Theorem | PO | Property |
|---|---|---|
| `txid_preimage_injective` | PO-5 evidence | Structural injectivity of the domain-separated txid transcript over `TxidShape`: version, input outpoints, outputs, locktime |
| `delta_tx_deterministic_ext` | PO-5 | Transition determinism |
| `delta_tx_preserves_no_double_spend` | PO-5 | No-double-spend preservation |
| `valid_tx_structural` | PO-5 evidence | Extractable structural transaction validator mirroring duplicate-input, missing-input, value-conservation, migration, and freeze checks |
| `valid_block_structural` | PO-5 evidence | Extractable structural block validator with sequential transition and block-cost checks |
| `cost_bounded_by_weight` | PO-7 | Cost bounded by transaction weight |
| `cost_equals_weight` | PO-7 | Exact equality for the modeled weight function |
| `block_cost_bounded_by_weights` | PO-7 | Block-level cost bound |

`TxidPreimage.v` defines the extractable txid transcript and proves injectivity
over the committed fields. The theorem is intentionally scoped to `TxidShape`,
not full `Transaction`, because witness bytes are not part of txid computation.
`extraction/TxidExtraction.v`, `extraction/ExtractTxidVectors.v`, and
`extraction/txid_refinement.ml` compare that transcript against Rust's
`txid_preimage` over count-delimited transaction matrices. Separately,
`extraction/TransitionExtraction.v`, `extraction/ExtractTransitionVectors.v`, and
`extraction/transition_refinement.ml` expose and summarize structural transition
functions. The Rust counterpart
`../../examples/generate_transition_refinement.rs` calls `valid_tx`, `delta_tx`,
`valid_block`, `check_migration_rules`, `check_no_frozen_inputs`, `cost_tx`,
`weight_tx`, and `check_block_cost` over the same projected matrix. The matrix
covers missing inputs, duplicate inputs, value inflation, frozen legacy/taproot
spends at cutover, legacy output creation after activation, mixed inputs,
fee-preserving multi-input transactions, sequential intra-block dependencies,
intra-block double spends, and exact/over-limit block-cost boundaries.
`../../src/kani_proofs.rs` adds fifteen bounded source-level PO-5 harnesses
over deployed Rust transition control flow: six `valid_tx` structural cases,
five `delta_tx` removal/preservation/insertion/empty/full-spend-create cases, and four
`valid_block` empty/sequential/rejection cases. Under `cfg(kani)`, the UTXO map
is a deterministic fixed-capacity finite map and `compute_txid` is a bounded
structural model so the verifier is not forced through OS-randomized hash
seeding or SHA-256 internals. These harnesses complement the extracted matrix,
but do not constitute an unbounded source-level transition refinement proof,
nor do they prove SHA-256 txid collision resistance, PQ witness cryptographic
verification, compiler correctness, or toolchain correctness.
`../../verify_txid_refinement.sh` validates the optimized txid refinement binary
against the Coq-extracted txid transcript summary.
`../../verify_runtime_refinement.sh` separately validates the optimized runtime
refinement binary against independent references for the domain-separated
`txid_preimage`, SHA-256 `compute_txid` wiring, canonical UTXO snapshots, and
runtime `UtxoSet` insert/get/remove/`delta_tx` behavior through the explicit
`UtxoStore` extensional contract. This narrows the runtime txid/store
correspondence boundary without proving SHA-256 primitive correctness, store
backend internals, or compiler/toolchain correctness.

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
| Source-level Rust refinement | 5 PO-8 Kani harnesses in `../../src/kani_proofs.rs` prove bounded symbolic alignment between the Rust layout parser, public parser, consensus parser, trace hook, canonicality predicates, and oversize guard; 15 PO-5 harnesses verify bounded deployed `valid_tx`, `delta_tx`, and `valid_block` transition behavior |
| Compiled/runtime artifact validation | `../../verify_compiled_refinement.sh` builds release examples, compares their outputs against Coq-extracted summaries, and emits a source/binary hash certificate; `../../verify_txid_refinement.sh` validates txid preimage release behavior against Coq extraction; `../../verify_runtime_refinement.sh` validates txid/store runtime behavior against independent deterministic references |
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
- If full end-to-end PO-4 closure is required, prove or import a verified
  SHA-256 implementation/refinement and connect it to the deployed Rust
  `tagged_hash` implementation. The current extracted transcript refinement
  covers deterministic serialization/preimage assembly, not the SHA-256
  compression function, BIP341 mechanization, or compiler/toolchain correctness.
- If full end-to-end PO-5 closure is required, continue on the selected
  Coq-first path: move the consensus transition core toward verified/extracted
  source and keep Rust adapters thin. Verus, Creusot, or Prusti can then target
  adapter/store obligations, but they are not the primary path for proving
  consensus transition semantics. The current transition refinement covers
  structural transaction/block semantics over deterministic edge-case matrices,
  validates txid and transition release binaries against Coq-extracted
  summaries, checks bounded deployed `valid_tx`, `delta_tx`, and `valid_block`
  behavior with Kani, and validates runtime txid/store behavior against
  independent deterministic references; it does not prove SHA-256 primitive
  correctness/collision resistance, PQ witness cryptographic verification, or
  compiler/toolchain correctness.
- Connect the finite TLA+ PO-6 model to the Coq/Rust transition artifacts if the
  project requires a single cross-artifact proof ledger.

## Technical Debt

- Generated extraction files (`golden_vectors_extracted.ml`, `.mli`, `.cmi`,
  `.cmo`, and the `golden_vectors` binary) are build artifacts and should not be
  versioned.
- The stale, incomplete `TestSighash.v` duplicate was removed. `SighashV2.v` is
  the canonical PO-4 Coq artifact.
