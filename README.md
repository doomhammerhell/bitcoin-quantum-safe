# Toward Protocol-Level Quantum Safety in Bitcoin

A formal, adversarial, and invariant-driven treatment of what it actually takes to make Bitcoin quantum-safe at the consensus level — not at the wallet level, not at the "just use a post-quantum signature" level, but at the level where it matters: the state machine.

## What this is

This repository contains a research paper and supporting formal artifacts that model Bitcoin's consensus layer as a labeled transition system and prove, under explicit axioms, what protocol-level quantum safety requires and why it cannot be achieved without hard trade-offs.

This is not a proposal. This is not a BIP. This is a formal framework for reasoning about Bitcoin under quantum adversaries.

## What the paper proves

- **Invariant preservation.** Consensus invariants (no double spend, state consistency, determinism) are preserved across all valid transitions, under explicit collision-resistance assumptions on the transaction id function.
- **Authorization reduction.** Unauthorized spends of post-quantum-locked outputs imply a break of the underlying PQ signature scheme (EUF-CMA) or hash binding, via a tight, non-rewinding game-hopping reduction that holds in the quantum random oracle model.
- **Replay exclusion.** Cross-input and cross-transaction witness replay attacks are excluded under a formally stated sighash commitment axiom.
- **Network resilience.** Adversarial network control (mempool observation, conflict injection, reorgs) does not bypass PQ authorization. The bound distinguishes block-constructing from observing adversaries.
- **Impossibility of free migration.** No cryptographic-only protocol transition can simultaneously preserve authorization safety and output liveness when lost keys exist.

## What the paper assumes (and does not prove)

- The sighash function satisfies a formally defined commitment property (injectivity modulo consensus-semantic equivalence, cross-input separation, field coverage). Verification against BIP 341 is deferred as an implementation obligation.
- The transaction id function is collision-resistant against QPT adversaries.
- The chosen PQ signature scheme is EUF-CMA secure against QPT adversaries, including in the QROM.
- Witness parsing is canonical, total, and deterministic.
- The mechanized spend predicate corresponds to the implementation used by consensus nodes.

All security theorems are conditional on these assumptions. Where an assumption is violated, the specific theorem that depends on it is identified in the paper.

## Repository structure

```
bitcoin-pq-safety/
├── paper/
│   ├── main.tex              # Paper source
│   ├── refs.bib              # Bibliography
│   └── Makefile              # Build via latexmk
├── formal/
│   ├── tla/
│   │   └── BitcoinPQ.tla     # TLA+ specification of UTXO transitions
│   └── coq/
│       └── README.md         # Planned Coq mechanization scope
├── models/
│   ├── state-machine.md      # State machine model summary
│   └── invariants.md         # Invariant catalog
├── CITATION.cff              # Citation metadata
├── .gitignore
└── README.md
```

## Build the paper

Requires TeX Live (2024+) with `latexmk`, `pdflatex`, and `bibtex`.

```sh
cd paper
make
```

Output: `paper/main.pdf`

Clean build artifacts:

```sh
cd paper
make clean
```

## Formal artifacts

### TLA+ (`formal/tla/`)

The `BitcoinPQ.tla` specification models UTXO state, transaction/block validation, and PQ authorization as a TLA+ module. Designed for finite-state exploration with TLC. Instantiate with small UTXO sets and bounded transaction counts to check invariants.

### Coq (`formal/coq/`)

Planned. The target is mechanization of the PQ spend predicate, witness parsing, and transition determinism (proof obligations PO-1 through PO-5 and PO-8 from the paper).

### Models (`models/`)

Markdown summaries of the state machine model and invariant catalog, extracted from the paper for quick reference.

## Citation

```bibtex
@article{giovani2026bitcoin,
  author  = {Mayckon Giovani},
  title   = {Toward Protocol-Level Quantum Safety in Bitcoin:
             A Formal, Adversarial, and Invariant-Driven Treatment},
  year    = {2026},
  note    = {Preprint}
}
```

Or use the `CITATION.cff` file for automated citation tools.

## Author

Mayckon Giovani

## License

This work is provided for academic review and discussion. All rights reserved by the author unless otherwise stated.
