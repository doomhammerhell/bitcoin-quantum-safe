# Toward Protocol-Level Quantum Safety in Bitcoin

A formal, adversarial, and invariant-driven treatment of what it actually takes to make Bitcoin quantum-safe at the consensus level — not at the wallet level, not at the "just use a post-quantum signature" level, but at the level where it matters: the state machine.

## What this is

This repository contains:

1. **A research paper** that models Bitcoin's consensus layer as a labeled transition system and proves, under explicit axioms, what protocol-level quantum safety requires and why it cannot be achieved without hard trade-offs.
2. **A Rust reference implementation** of the PQ witness protocol (SegWit v2, ML-DSA-44 FIPS 204) with 273 tests including 25 property-based tests.
3. **Coq mechanized proofs** covering 7 of 8 proof obligations (PO-1 through PO-7, plus PO-8 evidence).
4. **TLA+ model-checked specifications** of UTXO transitions (58,237 states, zero invariant violations).

This is not a proposal. This is not a BIP. This is a formal framework for reasoning about Bitcoin under quantum adversaries, with a reference implementation that demonstrates feasibility.

## What the paper proves

| Result | Theorem | Formal artifact |
|---|---|---|
| Invariant preservation | Thm 3, 4 | TLA+/TLC (2 models, zero violations) |
| Authorization reduction | Thm 5 | Game-hopping, tight, QROM-valid |
| Replay exclusion | Thm 6 | Sighash commitment (PO-4 executable evidence) |
| Network resilience | Thm 7 | Trace model with union bound |
| Impossibility of free migration | Thm 8, 9 | TLC counterexample |
| Spend predicate correctness | PO-1,2,3 | Coq (strengthened to full witness identity) |
| Transition determinism | PO-5 | Coq |
| Cost boundedness | PO-7 | Coq (exact equality: Cost = weight) |

## Proof obligation status

| PO | Property | Status | Artifact |
|---|---|---|---|
| PO-1 | Spend predicate totality | **Verified** | Coq `SpendPredPQ.v` |
| PO-2 | Spend predicate determinism | **Verified** | Coq `SpendPredPQ.v` |
| PO-3 | Parse canonicality | **Verified (strengthened)** | Coq `SpendPredPQ.v` |
| PO-4 | Sighash commitment | **Executable evidence** | Rust PBT (9 property tests) |
| PO-5 | Transition determinism | **Verified** | Coq `UTXOTransitions.v` |
| PO-6 | Invariant preservation | **Model-checked** | TLA+/TLC (2 models) |
| PO-7 | Cost boundedness | **Verified** | Coq `UTXOTransitions.v` |
| PO-8 | Implementation correspondence | **Strong evidence** | Coq `VarintConcrete.v` + golden vectors + Rust PBT |

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
│   ├── sighash.rs                  # Sighash v2 with BIP 340-style tagged hashes
│   ├── migration.rs                # Migration_Controller (3-phase state machine)
│   ├── weight.rs                   # Weight_Accountant, block cost invariant
│   ├── freeze.rs                   # Freeze_Enforcer for unmigrated outputs
│   ├── params.rs                   # Consensus parameters (C_MAX, witness sizes)
│   └── tests/mod.rs                # 268 unit + property-based tests
├── tests/
│   └── integration.rs              # 4 end-to-end integration tests
├── formal/
│   ├── coq/
│   │   ├── SpendPredPQ.v           # PO-1, PO-2, PO-3 (varint model)
│   │   ├── UTXOTransitions.v       # PO-5, PO-7 (UTXO model, cost model)
│   │   ├── VarintConcrete.v        # PO-8 (Bitcoin compact-size varint, golden vectors)
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
├── Cargo.toml
├── CITATION.cff
└── LICENSE
```

## Build instructions

### Prerequisites

| Tool | Version | Purpose |
|---|---|---|
| Rust | 1.70+ | Reference implementation |
| Rocq/Coq | 9.x (or Coq 8.18+) | Mechanized proofs |
| Java | 17+ | TLC model checker |
| TeX Live | 2024+ | Paper compilation |

### Rust implementation

```sh
# Build
cargo build

# Run all 273 tests (268 unit/property + 4 integration + 1 doc-test)
cargo test

# Lint
cargo clippy
```

The implementation uses the `fips204` crate for NIST FIPS 204 ML-DSA-44 signatures (not the pre-standard Dilithium2).

### Coq proofs

```sh
cd formal/coq

# Compile all 3 modules (SpendPredPQ.v, UTXOTransitions.v, VarintConcrete.v)
make

# Clean build artifacts
make clean
```

Requires Rocq 9.x. The `VarintConcrete.v` module prints golden test vectors via `Compute` during compilation — these match the Rust implementation byte-for-byte.

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

| Category | Count | Description |
|---|---|---|
| Encoding unit tests | 53 | Varint, witness serialize/parse, multisig encoding |
| Spend predicate tests | 16 | SpendPred_PQ single-sig + multisig with real ML-DSA-44 |
| Sighash tests | 17 | Tagged hashes, field coverage, domain separation |
| Migration tests | 24 | Phase transitions, boundary conditions, freeze |
| Weight tests | 25 | Cost function, block invariant, budget exclusion |
| Validation tests | 20 | ValidTx, DeltaTx, ValidBlock |
| Property-based tests | 25 | All 16 correctness properties + 9 PO-4 sighash tests |
| PO-8 correspondence | 19 | Varint axioms, parse injectivity, golden vectors |
| Adversarial boundary | 3 | Cross-input replay, cross-tx replay, commitment binding |
| Integration tests | 4 | Full migration, mixed blocks, multisig, activation |
| **Total** | **273** | |

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
