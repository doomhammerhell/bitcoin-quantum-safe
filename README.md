# Toward Protocol-Level Quantum Safety in Bitcoin

A formal, adversarial, and invariant-driven treatment of what it actually takes to make Bitcoin quantum-safe at the consensus level — not at the wallet level, not at the "just use a post-quantum signature" level, but at the level where it matters: the state machine.

## What this is

This repository contains:

1. **A research paper** that models Bitcoin's consensus layer as a labeled transition system and proves, under explicit axioms, what protocol-level quantum safety requires and why it cannot be achieved without hard trade-offs.
2. **A Rust reference implementation** of the PQ witness protocol (SegWit v2, ML-DSA-44 FIPS 204) with unit, integration, property-based, and golden-vector tests.
3. **Coq mechanized artifacts** for the spend predicate, UTXO transition, cost model, sighash model, Coq-extracted/Rust sighash transcript refinement, Coq-extracted/Rust UTXO transition refinement, bounded PO-8 extraction evidence, Kani source-level bounded Rust refinement harnesses for the witness parser, and compiled-artifact translation validation against the Coq-extracted summaries.
4. **TLA+ model-checked specifications** of UTXO transitions (58,237 states, zero invariant violations).

This is not a proposal. This is not a BIP. This is a formal framework for reasoning about Bitcoin under quantum adversaries, with a reference implementation that demonstrates feasibility.

## What the paper proves

| Result | Theorem | Formal artifact |
|---|---|---|
| Invariant preservation | Thm 3, 4 | TLA+/TLC (2 models, zero violations) |
| Authorization reduction | Thm 5 | Game-hopping, tight, QROM-valid |
| Replay exclusion | Thm 6 | Sighash commitment assumption (PO-4 verified Coq model + transcript refinement + Rust PBT) |
| Network resilience | Thm 7 | Trace model with union bound |
| Impossibility of free migration | Thm 8, 9 | TLC counterexample |
| Spend predicate correctness | PO-1,2,3 | Coq (strengthened to full witness identity) |
| Transition determinism | PO-5 | Coq + Coq-extracted/Rust transition refinement |
| Cost boundedness | PO-7 | Coq (exact equality: Cost = weight) |

## Proof obligation status

| PO | Property | Status | Artifact |
|---|---|---|---|
| PO-1 | Spend predicate totality | **Verified** | Coq `SpendPredPQ.v` |
| PO-2 | Spend predicate determinism | **Verified** | Coq `SpendPredPQ.v` |
| PO-3 | Parse canonicality | **Verified (strengthened)** | Coq `SpendPredPQ.v` |
| PO-4 | Sighash commitment | **Verified model + transcript refinement + executable evidence** | Coq `SighashV2.v` under SHA-256 collision-resistance axiom + Coq-extracted/Rust preimage transcript refinement + Rust PBT |
| PO-5 | Transition determinism | **Verified model + transition refinement evidence** | Coq `UTXOTransitions.v` + Coq-extracted/Rust transition refinement over structural edge-case matrices |
| PO-6 | Invariant preservation | **Model-checked** | TLA+/TLC (2 models) |
| PO-7 | Cost boundedness | **Verified** | Coq `UTXOTransitions.v` |
| PO-8 | Implementation correspondence | **Bounded extraction + source-level + compiled-artifact evidence** | Coq `VarintConcrete.v` concrete canonicality/injectivity + exhaustive u16 varint refinement + witness-level consensus-domain refinement matrix + executable consensus-size guard + extracted serializer + 7 golden vectors + Kani harnesses over `src/encoding.rs` + release-binary refinement validation + Rust PBT |

The detailed status ledger, including assumptions and residual proof gaps, is
maintained in [`PROOF_OBLIGATIONS.md`](PROOF_OBLIGATIONS.md).

## Repository structure

```
├── paper/
│   ├── main.tex                    # Paper source (LaTeX)
│   ├── refs.bib                    # Bibliography
│   └── Makefile                    # Build via pdflatex + bibtex
├── src/                            # Rust reference implementation
│   ├── lib.rs                      # Public API, ValidTx, DeltaTx, ValidBlock
│   ├── types.rs                    # Core types: Commitment, Transaction, UtxoSet
│   ├── encoding.rs                 # Varint, witness serialize/parse (single + multisig)
│   ├── spend_pred.rs               # SpendPred_PQ (single-sig + multisig, FIPS 204)
│   ├── sighash.rs                  # Sighash v2 transcript/preimage construction with BIP 340-style tagged hashes
│   ├── kani_proofs.rs              # Source-level bounded PO-8 Rust refinement harnesses
│   ├── migration.rs                # Migration_Controller (3-phase state machine)
│   ├── weight.rs                   # Weight_Accountant, block cost invariant
│   ├── freeze.rs                   # Freeze_Enforcer for unmigrated outputs
│   ├── params.rs                   # Consensus parameters (C_MAX, witness sizes)
│   └── tests/mod.rs                # 274 unit + property-based tests
├── tests/
│   └── integration.rs              # 4 end-to-end integration tests
├── formal/
│   ├── coq/
│   │   ├── SpendPredPQ.v           # PO-1, PO-2, PO-3 (varint model)
│   │   ├── UTXOTransitions.v       # PO-5, PO-7 (UTXO model, cost model, structural validators)
│   │   ├── VarintConcrete.v        # PO-8 (compact-size varint through 0xFD/u16)
│   │   ├── SighashV2.v             # PO-4 verified model + extractable transcript function
│   │   ├── extraction/             # Coq extraction drivers + PO-4/PO-5/PO-8 refinement harnesses
│   │   └── Makefile
│   └── tla/
│       ├── BitcoinPQ.tla           # Single-input model (492 states)
│       ├── BitcoinPQ.cfg
│       ├── BitcoinPQ_Migration.cfg # Migration dilemma counterexample
│       ├── BitcoinPQMulti.tla      # Multi-input model (58,237 states)
│       ├── BitcoinPQMulti.cfg
│       ├── BitcoinPQMulti_Freeze.cfg
│       └── Makefile
├── models/
│   ├── state-machine.md            # State machine model summary
│   └── invariants.md               # Invariant catalog
├── PROOF_OBLIGATIONS.md            # Authoritative proof-status ledger
├── verify_source_refinement.sh      # Kani source-level bounded Rust verification
├── verify_compiled_refinement.sh    # Release-binary PO-8 translation validation
├── verify_sighash_refinement.sh     # Release-binary PO-4 transcript validation
├── verify_transition_refinement.sh  # Release-binary PO-5 transition validation
├── Cargo.toml
├── CITATION.cff
└── LICENSE
```

## Build instructions

### Prerequisites

| Tool | Version | Purpose |
|---|---|---|
| Rust | 1.70+ | Reference implementation |
| Kani | 0.67.0 | Source-level bounded Rust refinement harnesses |
| Rocq/Coq | 8.18+ or 9.x | Mechanized proofs |
| Java | 17+ | TLC model checker |
| TeX Live | 2024+ | Paper compilation |

### Rust implementation

```sh
# Build
cargo build

# Run the full Rust test suite
cargo test

# Lint
cargo clippy

# Install Kani once, if needed
cargo install --locked kani-verifier --version 0.67.0

# Run source-level bounded parser refinement harnesses
./verify_source_refinement.sh
```

The implementation uses the `fips204` crate for NIST FIPS 204 ML-DSA-44 signatures (not the pre-standard Dilithium2). The Kani harnesses verify the deployed Rust parser source over bounded symbolic byte arrays and check that the allocation-free layout parser, public `parse_witness`, consensus-domain parser, trace instrumentation, and canonicality predicates remain aligned. The compiled-refinement scripts are run after `build_extraction.sh`: `verify_compiled_refinement.sh` validates optimized release binaries against the generated Coq-extracted PO-8 summaries, `verify_sighash_refinement.sh` validates the optimized Rust sighash transcript generator against the Coq-extracted PO-4 transcript summary, and `verify_transition_refinement.sh` validates the optimized Rust UTXO transition refinement generator against the Coq-extracted PO-5 transition summary. They emit certificates with toolchain, source, lockfile, binary, and generated-output hashes. This is translation validation of the compiled artifacts, not a proof of `rustc` or LLVM correctness.

### Coq proofs

```sh
cd formal/coq

# Compile all core modules
make

# Build bounded PO-8 extraction artifacts and compare with Rust
cd ../..
./build_extraction.sh

# Validate compiled release examples against Coq-extracted refinement summaries
./verify_compiled_refinement.sh

# Validate compiled sighash transcript construction against Coq extraction
./verify_sighash_refinement.sh

# Validate compiled UTXO transition behavior against Coq extraction
./verify_transition_refinement.sh

# Clean build artifacts
cd formal/coq
make clean
```

Requires Coq 8.18+ or Rocq 9.x. The imports use `From Coq Require Import` which is compatible with both. `VarintConcrete.v` proves the compact-size varint axioms for the modeled range `0..=65535`, proves concrete witness canonicality/injectivity for the bounded parser/serializer, proves that the protocol witness cap `MAX_WITNESS_SIZE = 16000` remains inside that range, proves that the consensus-domain parser equals the byte-level parser below the cap and rejects above it, and prints representative `Compute` values. `SighashV2.v` proves the modeled Sighash v2 commitment property under the SHA-256 collision-resistance axiom and exposes `sighash_preimage_from_hashes`, which separates deterministic transcript assembly from the cryptographic hash assumption for extraction. `UTXOTransitions.v` proves PO-5/PO-7 model properties and exposes structural `valid_tx`, `valid_block`, migration/freeze, `delta_tx`, and cost functions for extraction. `build_extraction.sh` generates seven bounded witness vectors from the Coq-extracted serializer and compares them byte-for-byte against the Rust generator; it exhaustively compares Coq-extracted varint encode/decode behavior against Rust over every modeled value `0..=65535` plus canonical rejection cases; it compares extracted witness `serialize`/`parse`/consensus-domain parse/canonicality behavior plus parser decision traces against Rust over a deterministic boundary/rejection matrix and 111,111 symbolic bounded witnesses; it compares the Coq-extracted sighash preimage transcript summary against Rust's deployed transcript construction; and it compares the Coq-extracted UTXO transition summary against Rust's deployed transition, migration, freeze, and cost functions over deterministic structural edge-case matrices. `verify_source_refinement.sh` then verifies five Kani harnesses over the Rust source-level witness parser. `verify_compiled_refinement.sh` builds the release PO-8 refinement executables and validates their generated outputs against the same Coq-extracted summaries. `verify_sighash_refinement.sh` separately builds the release sighash refinement executable and validates its output against the Coq-extracted transcript summary. `verify_transition_refinement.sh` builds the release transition refinement executable and validates its output against the Coq-extracted transition summary. Rust separately implements and tests the `0xFE` and `0xFF` CompactSize ranges; those ranges are outside the current Coq proof boundary for general-purpose CompactSize, and are rejected by the executable consensus-domain witness parser while the witness cap remains below `65535`.

### TLA+ model checking

```sh
cd formal/tla

# Download TLC if not present
curl -sL -o tla2tools.jar \
  "https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"

# Check structural invariants — single-input model (should PASS)
make check
# Result: 492 states, 260 distinct, zero violations

# Check structural invariants — multi-input model (should PASS)
make check-multi
# Result: 58,237 states, 6,365 distinct, zero violations

# Check migration dilemma — single-input (should FAIL with counterexample)
make check-migration

# Check freeze enforcement — multi-input (should FAIL with counterexample)
make check-multi-freeze

# Run all passing checks
make check-all
```

### Paper

```sh
cd paper
make          # or: pdflatex main.tex && bibtex main && pdflatex main.tex && pdflatex main.tex
make clean
```

## Test summary

The table groups security-relevant test intent. `cargo test -- --list` is the
authoritative source for the exact current test-case count.

| Category | Count | Description |
|---|---|---|
| Encoding unit tests | 54 | Varint, witness serialize/parse, consensus-domain guard, multisig encoding |
| Spend predicate tests | 16 | SpendPred_PQ single-sig + multisig with real ML-DSA-44 |
| Sighash tests | 27 | Tagged hashes, transcript layout, field coverage, domain separation |
| Migration tests | 24 | Phase transitions, boundary conditions, freeze |
| Weight tests | 25 | Cost function, block invariant, budget exclusion |
| Validation tests | 20 | ValidTx, DeltaTx, ValidBlock |
| Property-based tests | 34 | Core protocol, PO-4, PO-8, migration, cost, and parser properties |
| PO-8 correspondence | 28 | Varint axioms, parse injectivity, consensus-domain guard, trace alignment, bounded golden vectors |
| Source-level refinement | 5 | Kani symbolic bounded harnesses over Rust witness parser/layout/canonicality |
| Compiled-artifact refinement | 2 | Release-binary validation against Coq-extracted PO-8 and PO-4 transcript summaries |
| Consensus parameter guards | 1 | `MAX_WITNESS_SIZE <= u16::MAX` formal-domain guard |
| Adversarial boundary | 3 | Cross-input replay, cross-tx replay, commitment binding |
| Integration tests | 4 | Full migration, mixed blocks, multisig, activation |

## Citation

```bibtex
@article{giovani2026bitcoin,
  author  = {Mayckon Giovani},
  title   = {Toward Protocol-Level Quantum Safety in Bitcoin:
             A Formal, Adversarial, and Invariant-Driven Treatment},
  year    = {2026},
  note    = {Preprint, with Coq-mechanized proofs and TLA+ model checking}
}
```

## Author

Mayckon Giovani

## License

MIT License. See [LICENSE](LICENSE) for details.
