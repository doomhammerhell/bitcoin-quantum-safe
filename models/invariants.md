# Consensus Invariants

This document summarizes the invariants defined and proven in the paper (Section 4).

## Safety Invariants

### NoDoubleSpend

Every outpoint is removed from the UTXO set at most once across any execution trace.

```
∀ op: op is removed from U_t at most once across the trace
```

### StateConsistency

Every outpoint not in the current UTXO set either never existed or has been spent.

```
∀ op: op ∉ dom(U_t) ⟹ op never existed ∨ op has been spent
```

### Determinism

Valid transactions produce a unique successor state.

```
∀ U, tx: ValidTx(U, tx) = 1 ⟹ ∃! U' such that U' = δ_Tx(U, tx)
```

### Authorization Integrity

No QPT adversary can produce an unauthorized spend with non-negligible probability.

```
∀ A_q ∈ QPT: Adv_Auth^{A_q}(λ) ≤ negl(λ)
```

### Block Cost Bound

Total verification cost per block is bounded.

```
∀ B: ValidBlk(U, B) = 1 ⟹ Σ_{tx ∈ B} Cost(tx) ≤ C_max
```

## Preservation Theorems

### Theorem (Invariant preservation under δ_Tx)

If U satisfies all invariants and ValidTx(U, tx) = 1, then δ_Tx(U, tx) satisfies all invariants. Assumes collision resistance of h.

### Theorem (Invariant preservation under δ_Blk)

If U satisfies all invariants and ValidBlk(U, B) = 1, then δ_Blk(U, B) satisfies all invariants. By induction on the transaction sequence.

### Corollary (Global invariant preservation)

For any execution trace starting from a valid genesis state, every reachable state satisfies all invariants.

## Migration Invariants

### Migration Monotonicity

After the migration announcement height H_a (enforced by consensus), the PQ fraction ρ(U) is monotonically non-decreasing.

```
∀ t' > t ≥ H_a: ρ(U_{t'}) ≥ ρ(U_t)
```

### No-Free-Migration (Impossibility)

Under cryptographic-only authorization, no protocol transition simultaneously preserves safety and liveness for all outputs when lost keys exist.
