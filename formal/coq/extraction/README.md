# PO-4/PO-5/PO-8 Extraction and Refinement Vectors

This directory contains the Coq/Rust extraction-boundary correspondence evidence
used by CI. For PO-8 it covers bounded witness encoding, varint, consensus-domain
parser, canonicality, and parser-trace refinement. For PO-4 it covers deterministic
Sighash v2 transcript/preimage serialization, separated from the SHA-256
collision-resistance axiom. For PO-5 it covers txid preimage serialization,
structural UTXO transition,
transaction validation, block validation, migration/freeze, and cost refinement
against the deployed Rust transition functions. The repository-level source
proof layer is the Kani harness set in `../../../src`: PO-8 parser/layout
alignment plus bounded PO-5 `valid_tx`, `delta_tx`, and `valid_block`
transition harnesses. A separate runtime-refinement layer validates txid
preimage/hash wiring and runtime UTXO-store behavior against deterministic
references. The compiled-artifact
validation layers are `../../../verify_compiled_refinement.sh`,
`../../../verify_sighash_refinement.sh`, and
`../../../verify_txid_refinement.sh`, and
`../../../verify_transition_refinement.sh`; runtime txid/store validation is
`../../../verify_runtime_refinement.sh`.

## Source of Truth

- `WitnessExtraction.v` exposes the concrete Coq witness serializer/parser from
  `VarintConcrete.v` for extraction. It also exports semantic canonicality
  checkers and consensus-domain checkers with
  `is_canonical_witness_extract_sound`,
  `is_canonical_witness_bytes_extract_sound`,
  `parse_consensus_witness_extract_sound`, and
  `is_canonical_consensus_witness_bytes_extract_sound`, so the helpers are not
  vacuous test stubs.
- `ExtractWitnessVectors.v` is the extraction driver. Compiling it with `coqc`
  generates `golden_vectors_extracted.ml`.
- `golden_vectors.ml` is a handwritten JSON harness. It supplies deterministic
  test inputs and formats JSON, but witness bytes are produced by the extracted
  serializer.
- `varint_refinement.ml` exhaustively summarizes extracted Coq varint
  encode/decode behavior over `0..=65535`, including trailing-data decoding,
  non-canonical `0xFD` rejection, truncation, and unsupported-prefix rejection.
- `witness_refinement.ml` summarizes extracted Coq single-signature witness
  serialize/parse/consensus-domain parse/canonicality behavior over a
  deterministic matrix of u16 length boundaries and malformed witnesses. It also
  includes the extracted operational parser trace, whose result is proved equal
  to `parse_witness_concrete` by `parse_witness_trace_extract_result`. The matching
  Rust executable is `examples/generate_witness_refinement.rs`. Beyond the
  manual matrix, the harness enumerates all words of length `0..=5` over the
  modeled-domain symbolic byte alphabet `{0,1,2,3,4,31,32,33,252,253}`.
- `coq_vectors.json` is the checked-in output from the extracted serializer
  harness. `rust_vectors.json` at the repository root is the matching Rust
  output.
- `SighashExtraction.v` exposes the Coq Sighash v2 transcript constructors from
  `SighashV2.v`, including outpoint serialization, output serialization,
  spent-output serialization, and final preimage assembly with supplied 32-byte
  sub-hashes.
- `ExtractSighashVectors.v` is the extraction driver that generates
  `sighash_extracted.ml`.
- `sighash_refinement.ml` summarizes the extracted Coq sighash transcript
  behavior over a deterministic matrix. The matching Rust executable is
  `examples/generate_sighash_refinement.rs`.
- `TxidExtraction.v` exposes the Coq txid preimage transcript from
  `TxidPreimage.v`, including the domain tag, input outpoint serialization,
  output serialization, and full pre-hash transaction transcript.
- `ExtractTxidVectors.v` is the extraction driver that generates
  `txid_extracted.ml`.
- `txid_refinement.ml` summarizes the extracted txid preimage behavior over
  deterministic count-delimited transaction matrices. The matching Rust
  executable is `examples/generate_txid_refinement.rs`.
- `TransitionExtraction.v` exposes structural UTXO transition functions from
  `UTXOTransitions.v`: lookup/remove/add/delta, duplicate-input detection,
  input/output value sums, migration/freeze checks, structural `valid_tx`,
  structural `valid_block`, and cost functions.
- `ExtractTransitionVectors.v` is the extraction driver that generates
  `transition_extracted.ml`.
- `transition_refinement.ml` summarizes the extracted transition behavior over
  deterministic transaction, block, and block-cost matrices. The matching Rust
  executable is `examples/generate_transition_refinement.rs`.

## Formal Scope

### PO-4 Sighash Transcript Scope

The Sighash v2 Coq theorem remains a cryptographic model theorem under the
SHA-256 collision-resistance axiom. Extraction does not attempt to prove
SHA-256, the `sha2` Rust crate, BIP341 itself, or compiler correctness. Instead,
`sighash_preimage_from_hashes` isolates deterministic preimage construction from
the hash primitive:

- Coq supplies the final transcript assembler with explicit 32-byte outpoint and
  output sub-hashes.
- Rust exposes `sighash_v2_preimage_with_hashes` with the same contract.
- The refinement harness compares outpoint serialization, output serialization,
  spent-output serialization, and final preimage assembly across edge-case
  transactions, indices, values, and witness-byte differences.

This closes the implementation correspondence boundary for the modeled
transcript layout. What remains outside this extraction layer is SHA-256
primitive correctness, the collision-resistance assumption itself, and the
compiler/toolchain execution boundary.

### PO-5 UTXO Transition Scope

The PO-5 txid and transition refinement layer is structural and extensional.
`TxidPreimage.v` proves structural injectivity of the domain-separated txid
transcript over `TxidShape`: version, input outpoints, outputs, and locktime.
This is the correct projection because witness bytes are intentionally excluded
from txid computation. The Coq-extracted txid harness compares those preimage
bytes against Rust's deployed `txid_preimage` over count-delimited transaction
matrices.

Coq models UTXO sets as association lists indexed by `nat` outpoint IDs. Rust
models UTXO sets through the `UtxoSet`/`UtxoStore` extensional contract. The
harness uses a deterministic projection:
initial Coq IDs map to synthetic Rust outpoints; fresh Coq IDs map to
`compute_txid(tx), vout` for the corresponding Rust transaction output.

The summary compares only consensus-significant projected observations:
duplicate-input decisions, missing-input behavior, value conservation,
migration and freeze decisions, `valid_tx`, `delta_tx`, sequential
`valid_block`, block-cost checks, and selected UTXO membership/script/value
facts before and after transitions. It covers missing input, duplicate input,
value inflation, legacy output creation after `H_a`, frozen legacy and taproot
spends at `H_c`, mixed PQ/legacy inputs, fee-preserving multi-input cases,
sequential intra-block dependency, intra-block double spend, and exact/over
block-cost boundaries.

This does not prove SHA-256 txid collision resistance, UTXO-store backend internals,
PQ witness cryptographic verification, or compiler/toolchain correctness.
`verify_txid_refinement.sh` adds the txid release-binary validation layer and
emits `target/txid-refinement/txid_refinement_certificate.json`.
`verify_transition_refinement.sh` adds the transition release-binary validation layer and
emits `target/transition-refinement/transition_refinement_certificate.json`.
The source-level layer adds fifteen Kani bounded PO-5 harnesses for the
deployed Rust implementation: six `valid_tx` structural guard cases, five
`delta_tx` removal/preservation/insertion/empty/full-spend-create cases, and
four `valid_block` empty/sequential/rejection cases. Under `cfg(kani)`, the UTXO representation is
a deterministic fixed-capacity finite map and `compute_txid` is a bounded
structural model, so the verifier is not forced through OS-randomized hash
seeding or SHA-256 internals. Those harnesses complement the extracted matrix,
but are not an unbounded source-level transition proof and do not prove txid
collision resistance, UTXO-store backend internals, PQ witness cryptographic
verification, or compiler output.
`verify_runtime_refinement.sh` adds a runtime release-binary validation layer for
`txid_preimage`, `compute_txid`, canonical UTXO snapshots, and runtime
`UtxoSet` insert/get/remove/`delta_tx` behavior against independent deterministic
references. This narrows the txid/store implementation boundary, but it is not a
proof of SHA-256 primitive correctness, store backend internals, or compiler
output.

### PO-8 Witness Encoding Scope

The current Coq varint model covers Bitcoin CompactSize values in:

- `0..=252`: single-byte encoding.
- `253..=65535`: `0xFD` plus little-endian `u16`.

The seven golden vectors intentionally stay inside this domain:

1. `small`
2. `ml_dsa_44`
3. `slh_dsa_128s`
4. `empty`
5. `boundary_253`
6. `boundary_254`
7. `large_65535`

`large_65535` is a varint-domain boundary vector. It is not a spend-valid
witness under the current protocol cap because `MAX_WITNESS_SIZE = 16000`.

Rust separately implements and tests the `0xFE` and `0xFF` CompactSize ranges.
Those ranges remain outside the current Coq proof boundary for general-purpose
CompactSize. For the witness protocol subset, `VarintConcrete.v` now proves that
the consensus witness cap is inside the modeled range:

- `max_witness_size_within_varint_model`: `16000 <= max_u16`.
- `parse_witness_concrete_determines_serialize`.
- `parse_witness_concrete_injective`.
- `serialized_witness_size_bound_implies_modeled_lengths`.
- `parse_witness_concrete_size_bound_implies_modeled_lengths`.
- `parse_witness_concrete_bounded_canonical`.
- `parse_consensus_witness_concrete_sound`.
- `parse_consensus_witness_concrete_complete`.
- `parse_consensus_witness_concrete_oversized`.
- `parse_consensus_witness_concrete_bounded_canonical`.
- `is_canonical_consensus_witness_concrete_bytes_sound`.

The Rust side mirrors this with `max_witness_size_fits_formal_varint_domain` in
`src/params.rs`. The extraction pipeline additionally compares the exhaustive
Coq varint summary against `examples/generate_varint_refinement.rs`, which calls
the deployed Rust functions in `src/encoding.rs`, and compares the witness-level
summary against `examples/generate_witness_refinement.rs`, which calls
`serialize_witness`, `parse_witness`, `parse_consensus_witness`,
`parse_witness_trace`, `is_canonical_witness`, and
`is_canonical_consensus_witness` directly. `parse_witness_trace` shares the same
Rust implementation core as the public parser, so the comparison is over parser
transitions as well as final results. `parse_consensus_witness` is the executable
Rust guard that rejects syntactically valid but oversized witnesses outside the
current Coq witness domain. The symbolic bounded state-space currently adds
111,111 parser/canonicality cases.

The source-level Rust layer is intentionally separate from extraction:
`src/encoding.rs` now exposes an internal allocation-free witness layout parser
used by the public parser, consensus parser, and canonicality predicates, and
`src/kani_proofs.rs` verifies five bounded symbolic harnesses over that deployed
Rust source. The same proof module also verifies fifteen bounded PO-5
transition harnesses over deployed `valid_tx`, `delta_tx`, and `valid_block`
behavior. This closes the bounded source-level PO-8 parser-refinement step and
adds bounded source-level PO-5 transition evidence.

The compiled-artifact validation layer is also separate from extraction:
`verify_compiled_refinement.sh` builds the PO-8 Rust refinement examples in
release mode, executes those binaries, compares their JSON outputs against the
Coq-extracted summaries, and emits a certificate with source, lockfile, binary,
and generated-output hashes. `verify_sighash_refinement.sh` performs the same
release-binary validation pattern for the PO-4 sighash transcript executable.
`verify_transition_refinement.sh` performs the same release-binary validation
pattern for the PO-5 transition refinement executable. These give auditable
translation-validation artifacts for the produced binaries. The runtime
refinement validator follows the same certificate pattern for txid/store runtime
behavior, while still leaving compiler correctness outside the current artifact
boundary.
