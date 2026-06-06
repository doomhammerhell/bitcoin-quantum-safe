# Proof Obligation Ledger

This file is the authoritative status ledger for the formal artifacts in this
repository. Its purpose is to prevent proof-status drift between the paper,
README files, Coq modules, Rust tests, and CI.

## Status Semantics

| Status | Meaning |
|---|---|
| Verified | Machine-checked in Coq without using an admitted theorem for the named obligation. Cryptographic primitives may still be abstract parameters when the theorem is intentionally generic over the primitive. |
| Verified model + executable implementation evidence | Machine-checked for the Coq model under explicit cryptographic axioms, with executable tests covering the concrete implementation. This is stronger than a theorem-shape ledger but weaker than a full Coq-to-Rust refinement proof. |
| Verified model + transcript refinement + executable implementation evidence | Machine-checked for the Coq model under explicit cryptographic axioms, with a Coq-extracted deterministic transcript constructor compared against the Rust implementation and its optimized release binary. This narrows implementation correspondence for serialization/preimage assembly while still leaving cryptographic primitive implementation correctness and compiler correctness outside the artifact boundary. |
| Verified model + transition refinement evidence | Machine-checked for the Coq UTXO transition/cost model, with Coq-extracted structural transaction/block validators and transition functions compared against the Rust implementation and its optimized release binary over deterministic edge-case matrices. This narrows implementation correspondence for UTXO transition behavior while still leaving txid collision resistance, HashMap internals, cryptographic witness verification, and compiler correctness outside the artifact boundary. |
| Model-checked | Exhaustively checked by TLC over the finite model and configurations named below. This is not an unbounded Coq theorem. |
| Conditional/executable evidence | The theorem shape is formalized, but the proof depends on explicit axioms, admitted statements, or executable tests of the concrete implementation. |
| Bounded extraction evidence + source-level bounded Rust refinement + compiled-artifact validation | The bounded Coq parser/serializer model is machine-checked for canonicality/injectivity, the Coq-extracted varint encoder/decoder is exhaustively compared with Rust over `0..=65535`, witness serialization is compared byte-for-byte over explicit golden vectors, a witness-level refinement matrix plus symbolic bounded state-space compares Coq-extracted `serialize`/`parse`/consensus-domain parse/canonicality/operational-trace behavior against the Rust functions, Kani verifies bounded symbolic harnesses over the deployed Rust parser source, and release binaries are built and required to reproduce the Coq-extracted PO-8 summaries with source/binary hashes recorded in a certificate. This is stronger than source-only evidence, but it is not a proof of `rustc`, LLVM, linker, CPU, or OS correctness. |
| Open | The intended property is documented but not yet discharged by a formal artifact. |

## Obligation Status

| PO | Obligation | Security role | Current status | Primary artifacts | Explicit assumptions / boundary | Residual work |
|---|---|---|---|---|---|---|
| PO-1 | Spend predicate totality | Consensus validation must terminate with a boolean decision. | Verified | `formal/coq/SpendPredPQ.v` | `H`, `Vfy`, `encode_len`, and `decode_len` are abstract interfaces. | Instantiate the abstract varint interface into the spend-predicate module if a single closed Coq development is required. |
| PO-2 | Spend predicate determinism | Identical inputs must produce identical validation decisions across nodes. | Verified | `formal/coq/SpendPredPQ.v` | Same abstraction boundary as PO-1. | Same closure path as PO-1. |
| PO-3 | Witness parse canonicality | Prevents malleable witness encodings from producing ambiguous authorization state. | Verified, strengthened | `formal/coq/SpendPredPQ.v` | Depends on the six varint interface axioms. | Keep the concrete varint discharge synchronized with any encoding change. |
| PO-4 | Sighash commitment | The signed message must commit to all consensus-critical transaction fields and input position. | Verified model + transcript refinement + executable implementation evidence | `formal/coq/SighashV2.v`, `formal/coq/extraction/SighashExtraction.v`, `formal/coq/extraction/ExtractSighashVectors.v`, `formal/coq/extraction/sighash_refinement.ml`, `src/sighash.rs`, `examples/generate_sighash_refinement.rs`, `verify_sighash_refinement.sh`, Rust property tests | SHA-256 collision resistance is axiomatized. The Coq model machine-checks 4-byte and 8-byte little-endian reconstruction/injectivity, fixed-width serialization injectivity for outpoints/outputs/spent outputs, sub-hash injectivity, central `sighash_v2_injective`, cross-input separation, and field coverage. The theorem is scoped to well-formed transactions/spent outputs and u32 input indices with fixed-width fields, and is intentionally over consensus-significant input outpoints, not full witness-bearing `TxInput` records. `sighash_preimage_from_hashes` separates deterministic transcript assembly from SHA-256 and is extracted to OCaml; CI compares its summary against Rust's `serialize_sighash_*` and `sighash_v2_preimage*` functions over a deterministic transcript matrix, and `verify_sighash_refinement.sh` validates the optimized Rust refinement binary against the Coq-extracted summary with a hash certificate. Rust explicitly rejects indices that cannot be represented in the 4-byte consensus encoding before serialization. | Prove a verified SHA-256 implementation/refinement and compiler/toolchain correctness if full end-to-end PO-4 closure is required. A full BIP341 mechanization remains separate from this PQ Sighash v2 model. |
| PO-5 | Transition determinism | UTXO state transition must be deterministic under the same block/transaction input. | Verified model + transition refinement evidence | `formal/coq/UTXOTransitions.v`, `formal/coq/extraction/TransitionExtraction.v`, `formal/coq/extraction/ExtractTransitionVectors.v`, `formal/coq/extraction/transition_refinement.ml`, `src/lib.rs`, `src/migration.rs`, `src/freeze.rs`, `src/weight.rs`, `examples/generate_transition_refinement.rs`, `verify_transition_refinement.sh` | Coq proves the structural transition and cost model. The extractable PO-5 layer exposes `delta_tx`, structural `valid_tx`, structural `valid_block`, migration/freeze checks, and cost checks. CI compares Coq-extracted summaries against Rust's `valid_tx`, `delta_tx`, `valid_block`, `check_migration_rules`, `check_no_frozen_inputs`, `cost_tx`, `weight_tx`, and `check_block_cost` over deterministic matrices covering missing input, duplicate input, value inflation, frozen legacy spends, legacy output creation after `H_a`, post-cutover legacy/taproot rejection, mixed inputs, fee-preserving multi-input transactions, sequential intra-block dependency, intra-block double spend, and block-cost boundaries. The comparison uses an explicit projection from Coq `nat` outpoint IDs to synthetic Rust `OutPoint`s; fresh IDs map to `compute_txid(tx), vout`. It does not prove SHA-256 txid collision resistance, Rust `HashMap` internals, PQ witness cryptographic verification, or compiler/toolchain correctness. | Prove a stronger source-level Rust transition refinement, a verified txid implementation/refinement, and compiler/toolchain correctness if full end-to-end PO-5 closure is required. |
| PO-6 | Invariant preservation | UTXO structural invariants must survive valid transitions. | Model-checked | `formal/tla/BitcoinPQ.tla`, `formal/tla/BitcoinPQMulti.tla` | TLC covers the configured finite state spaces: single-input and multi-input models. PO-5 transition refinement strengthens the operational bridge from the Coq/Rust transition functions to the modeled transition classes, but does not turn PO-6 into an unbounded theorem. | Establish an unbounded theorem or cross-artifact refinement if the project requires proof beyond finite model checking. |
| PO-7 | Cost boundedness | PQ validation cost must remain within the block resource model. | Verified | `formal/coq/UTXOTransitions.v`, `src/weight.rs` | Coq proves exact equality for the modeled cost/weight function. | Maintain alignment if witness accounting or block cost constants change. |
| PO-8 | Implementation correspondence | The mechanized witness encoding model must correspond to bytes accepted/generated by implementation code. | Bounded extraction evidence + source-level bounded Rust refinement + compiled-artifact validation | `formal/coq/VarintConcrete.v`, `formal/coq/extraction/*`, `build_extraction.sh`, `verify_source_refinement.sh`, `verify_compiled_refinement.sh`, `compare_vectors.py`, `examples/generate_varint_refinement.rs`, `examples/generate_witness_refinement.rs`, `tests/po8_golden_vectors.rs`, `src/encoding.rs`, `src/kani_proofs.rs`, `src/params.rs` | Coq models CompactSize only for `0..=65535`. Rust implements `0xFE`/`0xFF`, but `MAX_WITNESS_SIZE = 16000 <= 65535`; Coq proves concrete bounded parser/serializer canonicality, parse injectivity, capped witness component bounds, and soundness of the extracted consensus-domain parser/canonicality predicates; Rust exposes and uses `parse_consensus_witness` / `is_canonical_consensus_witness`; CI exhaustively compares Coq-extracted varint encode/decode with Rust for all modeled values, CI compares Coq-extracted witness serialize/parse/consensus-domain parse/canonicality/operational-trace behavior against Rust over deterministic boundary/rejection cases plus 111,111 symbolic witnesses over the modeled-domain byte alphabet, CI runs Kani source-level bounded harnesses over the Rust layout parser, public parser, consensus parser, trace hook, canonicality predicates, and oversize guard, and CI builds release refinement binaries whose outputs must match the Coq-extracted summaries while emitting a hash certificate. | Full compiler-correctness proof remains open. Full CompactSize mechanization is optional for consensus-valid witness components while the witness cap remains below `65535`, but required if the cap is raised or if general-purpose CompactSize is claimed as verified. |

## PO-4 Boundary

PO-4 is no longer only a theorem over an isolated Coq model plus Rust property
tests. The current artifact boundary explicitly separates three layers:

- `formal/coq/SighashV2.v`: proves the modeled Sighash v2 commitment property
  under the SHA-256 collision-resistance axiom, including fixed-width
  little-endian injectivity, outpoint/output/spent-output serialization
  injectivity, sub-hash injectivity, central `sighash_v2_injective`,
  cross-input separation, and field coverage.
- `sighash_preimage_from_hashes`: isolates deterministic transcript assembly
  from SHA-256. This is the extractable structural function used for Rust
  transcript refinement; it assumes the 32-byte outpoint/output sub-hashes are
  supplied and proves agreement with the modeled `sighash_preimage`.
- `formal/coq/extraction/SighashExtraction.v`,
  `formal/coq/extraction/ExtractSighashVectors.v`, and
  `formal/coq/extraction/sighash_refinement.ml`: extract and summarize the Coq
  transcript constructors for outpoints, outputs, spent outputs, and final
  preimage assembly.

The Rust-side transcript boundary is explicit:

- `serialize_sighash_outpoints`, `serialize_sighash_outputs`, and
  `serialize_sighash_spent_output` expose the consensus bytes committed before
  sub-hashing.
- `sighash_v2_preimage_with_hashes` is the direct Rust counterpart of
  `sighash_preimage_from_hashes`; `sighash_v2_preimage` wires that transcript to
  the deployed tagged sub-hashes.
- `examples/generate_sighash_refinement.rs` generates the Rust summary over the
  same transcript matrix as the Coq-extracted OCaml harness.
- `verify_sighash_refinement.sh` builds the release Rust refinement executable,
  compares its output against `coq_sighash_refinement.json`, and writes
  `target/sighash-refinement/sighash_refinement_certificate.json` with
  toolchain, source, lockfile, binary, and output hashes.

This closes the previous source-level gap around deterministic preimage
serialization for the modeled transcript. It does not prove SHA-256's
implementation, SHA-256's collision resistance, BIP341 itself, `rustc`, LLVM,
the linker, CPU execution, or OS behavior. Those remain explicit trust
boundaries rather than implicit assumptions.

## PO-5 Boundary

PO-5 is no longer only a pure Coq determinism statement over an isolated UTXO
transition model. The current artifact boundary separates three layers:

- `formal/coq/UTXOTransitions.v`: proves deterministic structural transition
  functions and no-double-spend preservation for the association-list UTXO
  model, and defines extractable boolean checkers for structural `valid_tx`,
  structural `valid_block`, migration/freeze rules, and cost checks.
- `formal/coq/extraction/TransitionExtraction.v`,
  `formal/coq/extraction/ExtractTransitionVectors.v`, and
  `formal/coq/extraction/transition_refinement.ml`: expose the Coq transition
  functions to OCaml and summarize their behavior over a deterministic matrix of
  adversarial and boundary cases.
- `examples/generate_transition_refinement.rs`: builds the Rust counterpart of
  the same matrix using the deployed transition functions in `src/lib.rs`,
  `src/migration.rs`, `src/freeze.rs`, and `src/weight.rs`.

The matrix covers the consensus-relevant structural failure modes that matter
for UTXO transition safety: missing inputs, duplicate inputs, value inflation,
legacy output creation at and after `H_a`, frozen legacy and taproot spends at
`H_c`, mixed PQ/legacy inputs at cutover, fee-preserving multi-input
transactions, sequential intra-block dependencies, intra-block double spends,
and exact/over-limit block-cost boundaries.

The projection boundary is explicit. Coq uses `nat` outpoint IDs and
association-list UTXO sets. Rust uses `HashMap<OutPoint, Output>`. The harness
maps initial Coq IDs to synthetic `OutPoint`s and maps fresh Coq output IDs to
`compute_txid(tx), vout` for the corresponding Rust transaction. The summary
observes only extensional state facts over this projection: whether selected
abstract IDs are present and, if present, their script version and value.

`verify_transition_refinement.sh` builds the release Rust transition refinement
executable, compares its output against `coq_transition_refinement.json`, and
writes `target/transition-refinement/transition_refinement_certificate.json`
with toolchain, source, lockfile, binary, and output hashes. This closes the
current executable transition-correspondence boundary for the modeled structural
cases. It does not prove SHA-256 txid collision resistance, Rust `HashMap`
internals, PQ witness cryptographic verification, compiler correctness, linker
correctness, CPU correctness, or OS behavior.

PO-6 remains finite-state model-checked rather than an unbounded Coq theorem.
The PO-5 transition refinement evidence strengthens the operational bridge to
the Rust transition functions, but it does not by itself upgrade TLC invariant
preservation to an unbounded proof.

## PO-8 Boundary

The most important current trust boundary is PO-8. The Rust encoder implements
the full Bitcoin CompactSize domain, including `0xFE` and `0xFF`. The Coq model
currently proves the single-byte and `0xFD/u16` cases. This is acceptable only
for the verified witness subset because the consensus spend predicate rejects
witnesses above `MAX_WITNESS_SIZE`, and that constant is `16000`.

The formal closure added in `VarintConcrete.v` is:

- `max_witness_size_within_varint_model`: `16000 <= max_u16`.
- `parse_witness_concrete_determines_serialize`: every accepted concrete witness
  equals the canonical concrete serialization of its parsed components.
- `parse_witness_concrete_injective`: accepted concrete witnesses with the same
  parsed components are byte-identical.
- `serialized_witness_size_bound_implies_modeled_lengths`: serialized capped
  witnesses have public-key and signature lengths inside the Coq varint domain.
- `parse_witness_concrete_size_bound_implies_modeled_lengths`: successfully
  parsed capped witnesses also have component lengths inside the same domain.
- `parse_witness_concrete_bounded_canonical`: accepted capped byte-level
  witnesses are both canonical and inside the modeled u16 domain.
- `parse_consensus_witness_concrete_sound`: consensus parser acceptance implies
  the consensus size cap and byte-level parser acceptance.
- `parse_consensus_witness_concrete_complete`: below the consensus cap, the
  consensus parser is exactly the byte-level parser.
- `parse_consensus_witness_concrete_oversized`: above the consensus cap, the
  consensus parser rejects without parsing.
- `parse_consensus_witness_concrete_bounded_canonical`: consensus parser
  acceptance implies canonical bytes and modeled component lengths.
- `is_canonical_consensus_witness_concrete_bytes_sound`: consensus canonicality
  implies size-bound acceptance and canonical serialization.
- `varint_refinement.ml` plus `examples/generate_varint_refinement.rs`:
  exhaustive Coq-extracted vs Rust comparison for all `0..=65535` modeled
  varint values, trailing-data decoding, non-canonical `0xFD` rejection,
  truncation, and unsupported-prefix rejection.
- `witness_refinement.ml` plus `examples/generate_witness_refinement.rs`:
  Coq-extracted vs Rust transcript comparison for `serialize_witness`,
  `parse_witness`, `parse_consensus_witness`, `parse_witness_trace`,
  `is_canonical_witness`, and `is_canonical_consensus_witness` over a
  deterministic matrix of u16 length-boundary representatives,
  malformed/rejection witnesses, and all words of length `0..=5` over the
  modeled-domain symbolic byte alphabet
  `{0,1,2,3,4,31,32,33,252,253}`.

The executable guards added in Rust are:

- `max_witness_size_fits_formal_varint_domain` in `src/params.rs`.
- `parse_consensus_witness` and `is_canonical_consensus_witness` in
  `src/encoding.rs`; `spend_pred_pq` uses the consensus-domain parser.
- `parse_witness_layout` and `parse_consensus_witness_layout` in
  `src/encoding.rs`; these split parser acceptance/layout from byte-vector
  materialization, making canonicality allocation-free and giving the Rust proof
  harness a direct source-level state relation.
- `src/kani_proofs.rs` plus `verify_source_refinement.sh`: five Kani harnesses
  verify, over bounded symbolic byte arrays, that the layout parser and public
  parser agree, consensus parsing equals byte-level parsing below the cap, trace
  instrumentation preserves parser results, canonicality equals layout
  acceptance, and oversized witnesses are rejected before parsing.
- `verify_compiled_refinement.sh`: builds release refinement executables,
  compares their generated JSON outputs against the Coq-extracted golden,
  varint-refinement, and witness-refinement summaries, and writes
  `target/compiled-refinement/compiled_refinement_certificate.json` with
  toolchain, source, lockfile, binary, and output hashes. This validates the
  compiled artifact over the PO-8 modeled domains without claiming compiler
  correctness.

This narrows PO-8 to a concrete, protocol-relevant statement: current
consensus-valid witnesses do not need `0xFE` or `0xFF` length prefixes, the
bounded Coq parser/serializer has canonicality/injectivity proved directly, the
modeled varint subset is exhaustively refined against Rust, the
single-signature witness serializer/parser/consensus-domain parser/canonicality
behavior plus parser decision trace is compared against Rust at the
extracted-function boundary, Kani verifies the Rust parser source over a
bounded symbolic state space, and release binaries are translation-validated
against the Coq-extracted summaries. This closes the source-level bounded Rust
refinement layer and adds compiled-artifact validation for PO-8. It still does
not claim a proof of the Rust compiler, LLVM, linker, CPU, OS, or a verified
Coq-to-Rust translation for arbitrary Rust code generation.

## Removed Non-Authoritative Artifacts

`formal/coq/TestSighash.v` was a stale, incomplete duplicate outside the current
Coq Makefile. It has been removed; `formal/coq/SighashV2.v` is the canonical
PO-4 Coq artifact.
