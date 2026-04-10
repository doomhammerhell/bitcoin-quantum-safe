# Bitcoin Consensus State Machine Model

This document summarizes the formal state machine model defined in the paper (Section 2).

## State

The consensus state is a UTXO set:

```
U ∈ UTXO := OutPoint ⇀ Output
```

where:
- `OutPoint := {0,1}^256 × ℕ` — a (txid, index) pair
- `Output := Value × Script` — a satoshi value and a locking program

## Transitions

### Transaction transition

```
δ_Tx(U, tx) := (U \ {op_i}_i) ∪ {(h(tx), j) ↦ o_j}_j
```

Removes spent outpoints, adds newly created outpoints.

### Block transition

```
δ_Blk(U, B) := δ_Tx(···δ_Tx(δ_Tx(U, tx_0), tx_1)···, tx_{k-1})
```

Sequential application of transaction transitions.

## Validation

Transaction validation is a total predicate:

```
ValidTx(U, tx) = 1  ⟺
    Syntax(tx) ∧ NoDupInputs(tx) ∧ InputsExist(U, tx)
    ∧ ValueConservation(U, tx) ∧ WitnessOK(U, tx)
```

where `WitnessOK` requires every input's witness to satisfy the spend predicate under the sighash.

## Authorization

The PQ spend predicate:

```
SpendPred_PQ(P, m, w) = 1  ⟺
    Parse(w) = (pk, σ) ∧ H(pk) = P ∧ Vfy(pk, m, σ) = 1
```

Authorization is defined by oracle access:

```
Auth(U, tx) ⟺ ∀ input i: m_i ∈ Q_i
```

where `Q_i` is the set of messages queried to `Sign(sk_i, ·)`.

## Consensus-Semantic Equivalence

Two transactions are equivalent (`tx ≡_cs tx'`) if they agree on all consensus-critical fields. The canonical normalization function `Norm` maps each transaction to its unique equivalence class representative.

```
Norm(tx) = Norm(tx')  ⟺  tx ≡_cs tx'
```

## Axioms

The model depends on:
1. **Sighash commitment** (Definition 5 in paper): injectivity mod ≡_cs, cross-input separation, field coverage
2. **Txid collision resistance** (Definition 8 in paper): h(tx) ≠ h(tx') for tx ≠ tx' except with negligible probability
3. **EUF-CMA security** of the PQ signature scheme against QPT adversaries
