# PO-4/PO-8 Extraction and Refinement Vectors

This directory contains the Coq/Rust extraction-boundary correspondence evidence
used by CI. For PO-8 it covers bounded witness encoding, varint, consensus-domain
parser, canonicality, and parser-trace refinement. For PO-4 it covers deterministic
Sighash v2 transcript/preimage serialization, separated from the SHA-256
collision-resistance axiom. The repository-level source proof layer for PO-8 is
the Kani harness set in `../../../src`, and the compiled-artifact validation
layers are `../../../verify_compiled_refinement.sh` and
`../../../verify_sighash_refinement.sh`.

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

The source-level Rust layer is intentionally separate from extraction: `src/encoding.rs`
now exposes an internal allocation-free witness layout parser used by the public
parser, consensus parser, and canonicality predicates, and `src/kani_proofs.rs`
verifies five bounded symbolic harnesses over that deployed Rust source. This
closes the bounded source-level parser-refinement step.

The compiled-artifact validation layer is also separate from extraction:
`verify_compiled_refinement.sh` builds the PO-8 Rust refinement examples in
release mode, executes those binaries, compares their JSON outputs against the
Coq-extracted summaries, and emits a certificate with source, lockfile, binary,
and generated-output hashes. `verify_sighash_refinement.sh` performs the same
release-binary validation pattern for the PO-4 sighash transcript executable.
These give auditable translation-validation artifacts for the produced binaries,
while still leaving compiler correctness outside the current artifact boundary.
