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
| Verified model + txid/transition refinement + bounded source-level/runtime evidence | Machine-checked for the Coq UTXO transition/cost model and the Coq txid preimage transcript, with Coq-extracted txid/structural transaction/block validators, transition functions, block-application state transformers, and `CoqExtractedTransitionKernel` per-case structural report witnesses compared against explicit Rust structural entrypoints, `DeployedTransitionKernel` per-case reports, and optimized release binaries over deterministic edge-case matrices, Kani bounded source-level harnesses over deployed Rust `valid_tx_structural`, `delta_tx`, `valid_block_structural`, structural block-application behavior, and the `TransitionKernel` adapter boundary, and release-binary validation of txid preimage/SHA-256 wiring plus runtime UTXO-store extensional behavior against deterministic references. This narrows implementation correspondence for UTXO transition behavior while still leaving SHA-256 primitive correctness/collision resistance, cryptographic witness verification, compiler correctness, and the remaining unbounded-refinement path outside the current artifact boundary. |
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
| PO-5 | Transition determinism | UTXO state transition must be deterministic under the same block/transaction input. | Verified model + txid/transition refinement + bounded source-level/runtime evidence | `formal/coq/UTXOTransitions.v`, `formal/coq/TxidPreimage.v`, `formal/coq/extraction/TransitionExtraction.v`, `formal/coq/extraction/TxidExtraction.v`, `formal/coq/extraction/ExtractTransitionVectors.v`, `formal/coq/extraction/ExtractTxidVectors.v`, `formal/coq/extraction/transition_refinement.ml`, `formal/coq/extraction/transition_kernel_refinement.ml`, `formal/coq/extraction/txid_refinement.ml`, `src/lib.rs`, `src/transition_core.rs`, `src/types.rs`, `src/migration.rs`, `src/freeze.rs`, `src/weight.rs`, `src/kani_proofs.rs`, `examples/generate_transition_refinement.rs`, `examples/generate_transition_kernel_refinement.rs`, `examples/generate_txid_refinement.rs`, `examples/generate_runtime_refinement.rs`, `compare_transition_kernel_refinement.py`, `verify_transition_refinement.sh`, `verify_transition_kernel_refinement.sh`, `verify_txid_refinement.sh`, `verify_runtime_refinement.sh`, `verify_source_refinement.sh` | Coq proves the structural transition and cost model. Coq also mechanizes `txid_preimage` and proves `txid_preimage_injective` over the committed `TxidShape` projection: version, input outpoints, outputs, and locktime. This theorem is intentionally not over full `Transaction` equality because txid excludes witness bytes. The extractable PO-5 layer exposes `txid_preimage`, `delta_tx`, structural `valid_tx`, structural `valid_block`, `apply_block_transitions_structural`, `apply_valid_block_structural`, migration/freeze checks, and cost checks. Coq proves `apply_block_transitions_structural_equiv`, `apply_valid_block_structural_equiv`, and `apply_valid_block_structural_some_iff_valid`, connecting the boolean block predicate to the executable final-state transformer. CI compares Coq-extracted txid and transition outputs against Rust's `txid_preimage`, `valid_tx_structural`, `delta_tx`, `apply_block_transitions_structural`, `validate_and_apply_block_structural`, `valid_block_structural`, `check_migration_rules`, `check_no_frozen_inputs`, `cost_tx`, `weight_tx`, and `check_block_cost` over deterministic matrices covering count-delimited txid transcripts, missing input, duplicate input, value inflation, frozen legacy spends, the structurally valid PQ-spend boundary before witness verification, legacy output creation after `H_a`, post-cutover legacy/taproot rejection, mixed inputs, fee-preserving multi-input transactions, sequential intra-block dependency, intra-block double spend, final projected UTXO states, and block-cost boundaries. The full Rust `valid_tx`/`valid_block` path is intentionally stronger than this PO-5 structural layer because it additionally performs PQ witness cryptographic validation. The comparison uses an explicit projection from Coq `nat` outpoint IDs to synthetic Rust `OutPoint`s`; fresh IDs map to `compute_txid(tx), vout`. `src/transition_core.rs` now exposes a `TransitionKernel` contract, `StructuralTxReport`, `StructuralBlockReport`, and the deployed `DeployedTransitionKernel` adapter. This adapter delegates to the existing structural Rust entrypoints today, but makes the future Coq-extracted transition core substitution boundary explicit: same accept/reject decisions, same final UTXO snapshots, and same observable structural subdecisions. `formal/coq/extraction/transition_kernel_refinement.ml` wraps the Coq-extracted structural functions as a `CoqExtractedTransitionKernel` oracle and emits per-case JSON witnesses containing pre-state projections, transaction/block inputs, report fields, and projected final UTXO states. `examples/generate_transition_kernel_refinement.rs` emits the Rust `DeployedTransitionKernel` counterpart. `compare_transition_kernel_refinement.py` compares those witnesses by case name and emits semantic field-level diffs on mismatch. `verify_transition_kernel_refinement.sh` validates the optimized release binary for that report boundary and emits a dedicated transition-kernel certificate. Kani additionally checks twenty-one bounded PO-5 source-level harnesses: seven `valid_tx_structural` cases including the PQ-spend structural boundary, five `delta_tx` removal/preservation/insertion/empty/full-spend-create cases, four `valid_block_structural` cases covering empty block acceptance, sequential intra-block dependency, invalid-first-transaction rejection, and intra-block double-spend rejection, three structural block-application final-state/projection harnesses, and two `TransitionKernel` adapter report/projection harnesses. Runtime `compute_txid` computes SHA-256 over the domain-separated, self-delimiting `txid_preimage`, and runtime `UtxoSet` is now a wrapper implementing the explicit `UtxoStore` extensional contract rather than a public `HashMap` alias. `verify_txid_refinement.sh` validates the optimized txid refinement binary against the Coq-extracted txid summary. `verify_runtime_refinement.sh` validates the optimized runtime refinement binary against independent deterministic references for txid preimage/SHA-256 wiring and `UtxoSet` insert/get/remove/`delta_tx` behavior. Under `cfg(kani)`, txids use a deterministic bounded structural model and UTXO sets use a fixed-capacity finite map. This does not prove SHA-256 primitive correctness/collision resistance, PQ witness cryptographic verification, unbounded source-level refinement, or compiler/toolchain correctness. | Primary unbounded-refinement path is now Coq-first extracted/verified transition core plus thin Rust adapters. Verus/Creusot/Prusti remain secondary candidates for adapter/store obligations, not the primary proof path for consensus transition semantics. Full end-to-end closure still requires a verified SHA-256/txid implementation refinement and compiler/toolchain correctness or verified extraction. |
| PO-6 | Invariant preservation | UTXO structural invariants must survive valid transitions. | Model-checked | `formal/tla/BitcoinPQ.tla`, `formal/tla/BitcoinPQMulti.tla` | TLC covers the configured finite state spaces: single-input and multi-input models. PO-5 transition refinement and bounded source-level transition evidence strengthen the operational bridge from the Coq/Rust transition functions to the modeled transition classes, but do not turn PO-6 into an unbounded theorem. | Establish an unbounded theorem or cross-artifact refinement if the project requires proof beyond finite model checking. |
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
transition model. The current artifact boundary separates four layers:

- `formal/coq/UTXOTransitions.v`: proves deterministic structural transition
  functions and no-double-spend preservation for the association-list UTXO
  model, and defines extractable boolean checkers for structural `valid_tx`,
  structural `valid_block`, executable block-application state transformers,
  migration/freeze rules, and cost checks. The theorems
  `apply_block_transitions_structural_equiv`,
  `apply_valid_block_structural_equiv`, and
  `apply_valid_block_structural_some_iff_valid` prove that the optional
  final-state semantics is equivalent to the boolean block predicate.
- `formal/coq/TxidPreimage.v`: mechanizes the domain-separated txid transcript
  and proves `txid_preimage_injective` over the committed `TxidShape`
  projection: version, input outpoints, outputs, and locktime. The theorem
  deliberately does not claim full `Transaction` injectivity because witness
  bytes are excluded from txid computation.
- `formal/coq/extraction/TxidExtraction.v`,
  `formal/coq/extraction/ExtractTxidVectors.v`, and
  `formal/coq/extraction/txid_refinement.ml`: expose the Coq txid preimage
  constructor and summarize it over count-delimited transaction matrices.
- `formal/coq/extraction/TransitionExtraction.v`,
  `formal/coq/extraction/ExtractTransitionVectors.v`, and
  `formal/coq/extraction/transition_refinement.ml`: expose the Coq transition
  functions to OCaml and summarize both accept/reject behavior and projected
  final UTXO states over a deterministic matrix of adversarial and boundary
  cases.
- `formal/coq/extraction/transition_kernel_refinement.ml`: wraps the
  Coq-extracted structural functions as a `CoqExtractedTransitionKernel` oracle
  and emits per-case `StructuralTxReport`/`StructuralBlockReport` witnesses over
  the same deterministic projection boundary.
- `examples/generate_transition_refinement.rs`: builds the Rust counterpart of
  the same matrix using the deployed structural transition functions in
  `src/lib.rs`, `src/migration.rs`, `src/freeze.rs`, and `src/weight.rs`,
  including the public `apply_block_transitions_structural` and
  `validate_and_apply_block_structural` APIs. The full `valid_tx`/`valid_block`
  path remains the operational consensus layer because it additionally invokes
  PQ witness verification.
- `examples/generate_transition_kernel_refinement.rs`: builds the Rust
  `DeployedTransitionKernel` counterpart and emits directly comparable per-case
  report witnesses.
- `compare_transition_kernel_refinement.py`: compares the Coq and Rust
  TransitionKernel witnesses by case name and emits field-level semantic diffs
  for report, pre-state, transaction/block, and final-state mismatches.

The matrix covers the consensus-relevant structural failure modes that matter
for UTXO transition safety: missing inputs, duplicate inputs, value inflation,
the structurally valid PQ-spend boundary before witness verification, legacy
output creation at and after `H_a`, frozen legacy and taproot spends at `H_c`,
mixed PQ/legacy inputs at cutover, fee-preserving multi-input transactions,
sequential intra-block dependencies, intra-block double spends, and
exact/over-limit block-cost boundaries.

The projection boundary is explicit. Coq uses `nat` outpoint IDs and
association-list UTXO sets. Rust uses `UtxoSet` through the `UtxoStore`
extensional contract. The harness
maps initial Coq IDs to synthetic `OutPoint`s and maps fresh Coq output IDs to
`compute_txid(tx), vout` for the corresponding Rust transaction. The summary
observes only extensional state facts over this projection: whether selected
abstract IDs are present and, if present, their script version and value.
For block cases the summary records both the transition-only structural final
state (`apply_block_transitions_structural`) and the block-cost-valid structural
final state (`apply_valid_block_structural`/
`validate_and_apply_block_structural`). Full consensus acceptance with PQ
witness validation is deliberately outside this PO-5 structural summary.
The runtime txid path now exposes a domain-separated, self-delimiting
`txid_preimage` with explicit input/output counts, and `compute_txid` hashes
that transcript. Runtime UTXO-store comparison uses `canonical_utxo_entries`, a
key-sorted snapshot that observes store behavior extensionally rather than
through backend iteration order.
For Kani only, `cfg(kani)` replaces the runtime hash-backed `UtxoSet` with a
fixed-capacity deterministic finite-map model, uses a pairwise duplicate-input
scan, and replaces SHA-256 txid construction with a deterministic bounded
structural txid model. This avoids verifier-unsupported OS entropy,
standard-library map internals, and cryptographic primitive implementation
costs. It changes the proof harness representation of finite maps and txids,
not the normal runtime consensus path.

`verify_txid_refinement.sh` builds the release Rust txid refinement executable,
compares its output against `coq_txid_refinement.json`, and writes
`target/txid-refinement/txid_refinement_certificate.json` with toolchain,
source, lockfile, binary, and output hashes.

`verify_transition_refinement.sh` builds the release Rust transition refinement
executable, compares its output against `coq_transition_refinement.json`, and
writes `target/transition-refinement/transition_refinement_certificate.json`
with toolchain, source, lockfile, binary, and output hashes. This closes the
current executable correspondence boundary between the Coq structural transition
model and Rust structural entrypoints for the modeled cases, including
final-state projection for accepted structural block transitions. It does not
prove SHA-256 txid collision resistance, UTXO-store backend internals, PQ
witness cryptographic verification, compiler correctness, linker correctness,
CPU correctness, or OS behavior.

`verify_transition_kernel_refinement.sh` builds the optimized Rust
`generate_transition_kernel_refinement` executable, compares the resulting
`DeployedTransitionKernel` per-case report witnesses against
`coq_transition_kernel_refinement.json` using
`compare_transition_kernel_refinement.py`, and writes
`target/transition-kernel-refinement/transition_kernel_refinement_certificate.json`
with toolchain, source, lockfile, binary, input, and output hashes. This is the
dedicated release-binary certificate for the TransitionKernel adapter boundary:
the observed `StructuralTxReport` and `StructuralBlockReport` fields, selected
pre-state projections, transaction/block witnesses, and projected final UTXO
states match the Coq-extracted oracle over the modeled deterministic matrix. It
is not a proof of
the Rust compiler, LLVM, linker, CPU, OS, SHA-256, UTXO-store backend internals,
or PQ witness verification.

`verify_runtime_refinement.sh` builds the release runtime refinement executable,
checks `txid_preimage` and `compute_txid` against an independent transcript and
SHA-256 invocation, checks runtime `UtxoSet` insert/get/remove behavior against
a deterministic reference map, and checks `delta_tx` against the same reference
using canonical snapshots. It writes
`target/runtime-refinement/runtime_refinement_certificate.json` with toolchain,
source, binary, and generated-output hashes. This narrows the txid/store runtime
boundary, but it still does not prove SHA-256 primitive correctness/collision
resistance, store backend internals, compiler correctness, linker correctness, CPU
correctness, or OS behavior.

The chosen path for unbounded refinement is Coq-first verified/extracted
transition core plus thin Rust adapters. That keeps the consensus state-machine
semantics in the proof assistant and reduces Rust verification to adapter,
store, and cryptographic-primitive boundaries. Verus, Creusot, and Prusti remain
useful candidates for those Rust adapter/store obligations, but they are not the
primary path for proving the full consensus transition semantics. A Rust-first
unbounded proof would force the project through standard-library map behavior,
compiler MIR/LLVM boundaries, and evolving verifier support before the
consensus model itself is closed.

PO-6 remains finite-state model-checked rather than an unbounded Coq theorem.
The PO-5 transition refinement evidence and bounded source-level structural
transition harnesses strengthen the operational bridge to the Rust transition
functions, but they do not by themselves upgrade TLC invariant preservation to
an unbounded proof.

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
- `src/kani_proofs.rs` plus `verify_source_refinement.sh`: five PO-8 Kani
  harnesses verify, over bounded symbolic byte arrays, that the layout parser
  and public parser agree, consensus parsing equals byte-level parsing below the
  cap, trace instrumentation preserves parser results, canonicality equals
  layout acceptance, and oversized witnesses are rejected before parsing. The
  same source-level proof module adds twenty-one PO-5 bounded transition
  harnesses over `valid_tx_structural`, `delta_tx`, `valid_block_structural`,
  structural block-application final-state behavior, and the `TransitionKernel`
  adapter report/projection boundary.
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
