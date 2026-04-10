# Coq Mechanization (Planned)

This directory is reserved for Coq mechanization of the PQ spend predicate and witness parsing rules.

## Scope

The target proof obligations (from Section 11 of the paper) are:

- **PO-1**: Spend predicate totality
- **PO-2**: Spend predicate determinism
- **PO-3**: Witness parsing canonicality
- **PO-5**: Transition determinism
- **PO-8**: Implementation correspondence (extraction/bisimulation against production code)

## Status

Not yet started. This directory serves as a placeholder for the mechanization effort described in the paper.

## Approach

The planned approach is to:
1. Define `SpendPredPQ` as a Coq function over byte-level representations
2. Prove totality and determinism as Coq theorems
3. Define `Parse` and prove canonicality (injectivity on accepting domain)
4. Extract to OCaml/Rust and verify correspondence against Bitcoin Core's implementation
