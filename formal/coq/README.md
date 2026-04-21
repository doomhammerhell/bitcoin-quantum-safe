# Coq Mechanization: PQ Spend Predicate

Machine-checked proofs of proof obligations PO-1, PO-2, PO-3 from the paper.

## Verified Properties

| Theorem | PO | Property |
|---|---|---|
| `spend_pred_pq_total` | PO-1 | Totality: predicate always returns true or false |
| `spend_pred_pq_deterministic` | PO-2 | Determinism: same inputs, same output |
| `spend_pred_pq_deterministic_ext` | PO-2 | Extensional determinism |
| `parse_extracts` | PO-3 | Parse decomposes witness into (pk, sig) |
| `parse_canonical` | PO-3 | Parse output determines witness content |
| `spend_pred_pq_iff` | — | Complete characterization of acceptance |
| `spend_pred_pq_none_is_false` | — | Parse failure implies rejection |
| `spend_pred_pq_hash_mismatch` | — | Hash mismatch implies rejection |
| `spend_pred_pq_vfy_fail` | — | Verification failure implies rejection |

## Build

Requires Rocq/Coq 9.x (or Coq 8.18+).

```sh
make        # compile all proofs
make clean  # remove artifacts
```

## Design

The cryptographic primitives (`H`, `Vfy`) are axiomatized as parameters, matching the paper's approach: security theorems hold for any PQC-Sig satisfying EUF-CMA. The witness encoding uses a length-prefixed format. All functions are pure (no state, no randomness, no IO), so totality and determinism follow from Coq's type system — but we state them as explicit theorems for correspondence with the paper's proof obligations.

## Remaining Obligations

- PO-4 (sighash commitment): requires mechanizing BIP 341
- PO-5 (transition determinism): requires UTXO set formalization
- PO-7 (cost boundedness): requires concrete parameterization
- PO-8 (implementation correspondence): requires extraction to Rust/C++
