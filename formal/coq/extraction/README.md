# PO-4/PO-5/PO-6/PO-8 Extraction and Refinement Vectors

This directory contains the Coq/Rust extraction-boundary correspondence evidence
used by CI. For PO-8 it covers bounded witness encoding, varint, consensus-domain
parser, canonicality, and parser-trace refinement. For PO-4 it covers deterministic
Sighash v2 transcript/preimage serialization, separated from the SHA-256
collision-resistance axiom. For PO-5 it covers txid preimage serialization,
structural UTXO transition,
transaction validation, block validation, migration/freeze, and cost refinement
against the deployed Rust transition functions, plus PQ suite profile/activation
metadata refinement, plus PO-6 UTXO-domain/value
invariant witness refinement under the explicit Coq fresh-id theorem boundary, plus direct
`CoqExtractedTransitionKernel` per-case report refinement against the Rust
`DeployedTransitionKernel` adapter. The repository-level source
proof layer is the Kani harness set in `../../../src`: PO-8 parser/layout
alignment plus bounded PO-5 `valid_tx_structural`, `delta_tx`,
`valid_block_structural`, and structural block-application transition
harnesses, plus bounded checks for the Rust `TransitionKernel` adapter
projection boundary. A separate runtime-refinement layer validates txid
preimage/SHA-256 wiring and runtime UTXO-store behavior against deterministic
references. The compiled-artifact
validation layers are `../../../scripts/verification/verify_compiled_refinement.sh`,
`../../../scripts/verification/verify_sighash_refinement.sh`, and
`../../../scripts/verification/verify_txid_refinement.sh`, and
`../../../scripts/verification/verify_transition_refinement.sh`; TransitionKernel adapter validation
is `../../../scripts/verification/verify_transition_kernel_refinement.sh`; PO-6 invariant validation
is `../../../scripts/verification/verify_transition_invariant_refinement.sh`; runtime txid/store
validation is `../../../scripts/verification/verify_runtime_refinement.sh`; PQ profile validation is
`../../../scripts/verification/verify_pq_profile_refinement.sh`.

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
- `PQProfileExtraction.v` exposes the checked PQ suite profile/activation
  boundary from `../PQProfile.v` as extraction rows and boolean properties.
- `ExtractPQProfileVectors.v` is the extraction driver that generates
  `pq_profile_extracted.ml`.
- `pq_profile_refinement.ml` formats the Coq-extracted profile rows as
  structured JSON. The matching Rust executable is
  `examples/generate_pq_profile_refinement.rs`.
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
  structural `valid_block`, executable block-application final-state
  transformers, domain/value invariant observers, and cost functions.
- `ExtractTransitionVectors.v` is the extraction driver that generates
  `transition_extracted.ml`.
- `transition_refinement.ml` summarizes the extracted transition behavior over
  deterministic transaction, block, and block-cost matrices. The matching Rust
  executable is `examples/generate_transition_refinement.rs`.
- `transition_kernel_refinement.ml` wraps the extracted transition functions as
  a `CoqExtractedTransitionKernel` oracle and emits per-case
  `StructuralTxReport`/`StructuralBlockReport` witnesses over the same
  projection matrix. The matching Rust executable is
  `examples/generate_transition_kernel_refinement.rs`.
- `scripts/verification/compare_transition_kernel_refinement.py` is the semantic comparator for those
  witnesses. It reports mismatches by transaction/block case name and nested
  field path instead of relying on hash summaries or full-object dumps.
- `transition_invariant_refinement.ml` exposes the PO-6 UTXO-domain preservation
  and total-value non-increase theorem boundary as per-case structured
  witnesses. It reports pre-state domain uniqueness, pre-state total value,
  fresh-id/domain-bound applicability, accepted/rejected block results,
  final-state domain observations, final-state total value, spent-input
  absence, and explicit non-applicability reasons for freshness-boundary cases. The matching Rust
  executable is `examples/generate_transition_invariant_refinement.rs`.
- `scripts/verification/compare_transition_invariant_refinement.py` is the semantic comparator for
  the PO-6 invariant witnesses. It reports mismatches by block case name and
  nested field path, including theorem-applicability and boundary-reason fields.

## Formal Scope

### PQ Profile Activation Scope

The PQ profile refinement layer is a control-plane correspondence check, not a
cryptographic proof of ML-DSA or SLH-DSA. `PQProfile.v` proves that the tracked
FIPS 204 ML-DSA-44 primary profile and FIPS 205 SLH-DSA-128s fallback profile
fit the consensus witness cap, use distinct assumption families, and that only
ML-DSA-44 is consensus-enabled while SLH-DSA-128s lacks an implemented verifier.

The extraction harness turns those checked facts into a structured JSON summary
containing profile dimensions, witness sizes, implemented-verifier flags,
consensus-enabled flags, primary/fallback markers, and aggregate activation
properties. The Rust counterpart derives the same summary from `src/pq_profile.rs`.
CI compares the two summaries exactly, and `scripts/verification/verify_pq_profile_refinement.sh`
builds the optimized Rust summary executable and records source, binary, and
output hashes in `target/pq-profile-refinement/pq_profile_refinement_certificate.json`.

This closes the profile metadata correspondence boundary. It does not prove
FIPS primitive security, the correctness of signature verification libraries,
or compiler/toolchain correctness.

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
migration and freeze decisions, `valid_tx_structural`, `delta_tx`, sequential
`valid_block_structural`, transition-only structural block application,
block-cost-valid structural block application, block-cost checks, and selected
UTXO membership/script/value facts before and after transitions. It covers
missing input, duplicate input, value inflation, the structurally valid PQ-spend
boundary before witness verification, legacy output creation after `H_a`,
frozen legacy and taproot spends at `H_c`, mixed PQ/legacy inputs,
fee-preserving multi-input cases, sequential intra-block dependency,
intra-block double spend, projected final UTXO states, and exact/over block-cost
boundaries.

`../../../src/transition_core.rs` defines the Rust transition-kernel adapter
boundary used by the forward path to a Coq-first verified/extracted transition
core. The deployed adapter currently delegates to the structural Rust
entrypoints, but exposes stable transaction and block reports that a future
extracted kernel must match extensionally.
The extraction harness now makes that report boundary executable:
`transition_kernel_refinement.ml` computes the Coq-side reports through
`CoqExtractedTransitionKernel`, while
`examples/generate_transition_kernel_refinement.rs` computes the Rust-side
reports through `DeployedTransitionKernel`. The comparison observes report
fields, projected pre-states, transaction/block witnesses, and projected final
UTXO states, not internal map order or witness cryptographic checks.

This does not prove SHA-256 txid collision resistance, UTXO-store backend internals,
PQ witness cryptographic verification, or compiler/toolchain correctness.
`scripts/verification/verify_txid_refinement.sh` adds the txid release-binary validation layer and
emits `target/txid-refinement/txid_refinement_certificate.json`.
`scripts/verification/verify_transition_refinement.sh` adds the transition release-binary validation layer and
emits `target/transition-refinement/transition_refinement_certificate.json`.
`scripts/verification/verify_transition_kernel_refinement.sh` adds the TransitionKernel report
release-binary validation layer and emits
`target/transition-kernel-refinement/transition_kernel_refinement_certificate.json`.
On mismatch it invokes `scripts/verification/compare_transition_kernel_refinement.py`, which prints
field-level semantic diffs by case name.
The source-level layer adds twenty-one Kani bounded PO-5 harnesses for the
deployed Rust structural entrypoints: seven `valid_tx_structural` cases
including the PQ-spend structural boundary, five `delta_tx`
removal/preservation/insertion/empty/full-spend-create cases, and four
`valid_block_structural` empty/sequential/rejection cases plus three structural
block-application final-state/projection cases, plus two `TransitionKernel`
adapter report/projection cases. Under `cfg(kani)`, the UTXO representation is
a deterministic fixed-capacity finite map and `compute_txid` is a bounded
structural model, so the verifier is not forced through OS-randomized hash
seeding or SHA-256 internals. Those harnesses complement the extracted matrix,
but are not an unbounded source-level transition proof and do not prove txid
collision resistance, UTXO-store backend internals, PQ witness cryptographic
verification, or compiler output.
`scripts/verification/verify_runtime_refinement.sh` adds a runtime release-binary validation layer for
`txid_preimage`, `compute_txid`, canonical UTXO snapshots, and runtime
`UtxoSet` insert/get/remove/`delta_tx` behavior against independent deterministic
references. This narrows the txid/store implementation boundary, but it is not a
proof of SHA-256 primitive correctness, store backend internals, or compiler
output.

### PO-6 UTXO-Domain/Value Invariant Scope

PO-6 now has Coq theorems over the structural UTXO-domain invariant and the
total-value non-increase invariant in addition to TLC finite-state model
checking. `UTXOTransitions.v` defines the abstract domain and total value of an
association-list UTXO set and proves that accepted structural block application
preserves a duplicate-free final domain below the next fresh-id bound and cannot
increase total UTXO value:

- initial UTXO domain has no duplicate abstract outpoint IDs;
- every initial outpoint ID is strictly below the fresh-id base;
- `apply_valid_block_structural` accepts and returns a final state;
- the final UTXO domain remains duplicate-free and below
  `fresh_id + block_output_count block`.
- the final UTXO total value is less than or equal to the initial UTXO total
  value.

The economic theorem is non-increase, not exact equality. The structural
transaction rule permits implicit fee burn through `sum(outputs) <= sum(inputs)`;
therefore exact monetary-supply/fee accounting is a separate specification layer
if the protocol later requires it.

The extraction harness intentionally makes this precondition visible. Cases with
missing inputs or intra-block double spends are rejected-block witnesses; cases
where the fresh-id/domain-bound precondition is false are non-applicability
witnesses, not failed proofs. This keeps the txid/freshness/collision boundary
explicit: the Coq theorem does not derive fresh txids from SHA-256, and the Rust
projection does not pretend that a single abstract ID can safely represent both
an old UTXO and a newly created output.

`scripts/verification/verify_transition_invariant_refinement.sh` builds the optimized Rust invariant
witness executable, compares it against
`coq_transition_invariant_refinement.json` through
`scripts/verification/compare_transition_invariant_refinement.py`, and emits
`target/transition-invariant-refinement/transition_invariant_refinement_certificate.json`
with toolchain, input, binary, and generated-output hashes. This is operational
evidence for the structural-domain/value invariant boundary; it is not a proof
of full consensus invariant preservation, cryptographic witness verification,
txid collision resistance, store backend internals, exact monetary-supply/fee
accounting beyond the structural non-increase theorem, or compiler correctness.

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
Rust source. The same proof module also verifies twenty-one bounded PO-5
transition harnesses over deployed `valid_tx_structural`, `delta_tx`,
`valid_block_structural`, structural block-application behavior, and the
`TransitionKernel` adapter projection. This
closes the bounded source-level PO-8 parser-refinement step and adds bounded
source-level PO-5 structural transition evidence.

The compiled-artifact validation layer is also separate from extraction:
`scripts/verification/verify_compiled_refinement.sh` builds the PO-8 Rust refinement examples in
release mode, executes those binaries, compares their JSON outputs against the
Coq-extracted summaries, and emits a certificate with source, lockfile, binary,
and generated-output hashes. `scripts/verification/verify_sighash_refinement.sh` performs the same
release-binary validation pattern for the PO-4 sighash transcript executable.
`scripts/verification/verify_transition_refinement.sh` performs the same release-binary validation
pattern for the PO-5 transition/final-state refinement executable.
`scripts/verification/verify_transition_kernel_refinement.sh` performs the same validation pattern for
the PO-5 TransitionKernel per-case report executable.
`scripts/verification/verify_transition_invariant_refinement.sh` performs the same validation pattern
for the PO-6 UTXO-domain/value invariant witness executable. These give auditable
translation-validation artifacts for the produced binaries. The runtime
refinement validator follows the same certificate pattern for txid/store runtime
behavior, and `scripts/verification/verify_pq_profile_refinement.sh` applies the same certificate
pattern to the PQ profile activation summary, while still leaving compiler
correctness outside the current artifact boundary.
