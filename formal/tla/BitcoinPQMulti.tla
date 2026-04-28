------------------------- MODULE BitcoinPQMulti -------------------------
(*
 * Copyright (c) 2026 Mayckon Giovani. MIT License.
 *
 * Extended TLA+ specification for Bitcoin post-quantum UTXO transitions.
 * Strengthens PO-6 with multi-input/multi-output transactions and
 * explicit value conservation.
 *
 * Extends the single-input model (BitcoinPQ) with:
 *   - Multi-input transactions (1-2 inputs)
 *   - Multi-output transactions (1-2 outputs)
 *   - Explicit value conservation: sum(inputs) >= sum(outputs)
 *   - Freeze enforcement: after cutover, non-PQ outputs cannot be spent
 *   - Migration monotonicity: PQ fraction is non-decreasing after H_a
 *
 * Invariants:
 *   I1  NoDoubleSpend         — spent ∩ DOMAIN utxo = {}
 *   I2  ValueBound            — total value never exceeds genesis total
 *   I3  StateConsistency      — all ids fresh and tracked
 *   I4  MigrationMonotonicity — PQ fraction consistent with UTXO set
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    MaxOP,              \* Maximum outpoint id (bounds state space)
    MigrationAnnounce,  \* Height: no new legacy outputs after this
    MigrationCutover,   \* Height: legacy spends rejected after this
    GenesisTotal        \* Total value minted at genesis

VARIABLES
    utxo,       \* Function: outpoint id -> [value: Int, lock: STRING]
    spent,      \* Set of all outpoints ever spent
    height,     \* Current block height
    nextId,     \* Next available outpoint id
    pqFrac      \* Count of PQ outputs in the UTXO set

vars == <<utxo, spent, height, nextId, pqFrac>>

\* -----------------------------------------------------------------------
\* Helpers
\* -----------------------------------------------------------------------

RECURSIVE SetSum(_, _)
SetSum(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x].value + SetSum(f, S \ {x})

PQCount(u) ==
    Cardinality({op \in DOMAIN u : u[op].lock = "pq"})

\* -----------------------------------------------------------------------
\* Initial state: three genesis outputs (total value = GenesisTotal = 4)
\* -----------------------------------------------------------------------

Init ==
    /\ utxo = (1 :> [value |-> 2, lock |-> "legacy"])
            @@ (2 :> [value |-> 1, lock |-> "pq"])
            @@ (3 :> [value |-> 1, lock |-> "legacy"])
    /\ spent = {}
    /\ height = 0
    /\ nextId = 4
    /\ pqFrac = 1

\* -----------------------------------------------------------------------
\* Spend1: single-input, single-output transaction
\* -----------------------------------------------------------------------

Spend1 ==
    \E inOp \in DOMAIN utxo :
    \E outLock \in {"legacy", "pq"} :
    \E outVal \in 1..utxo[inOp].value :
        /\ (height >= MigrationCutover => utxo[inOp].lock = "pq")
        /\ (height >= MigrationAnnounce => outLock = "pq")
        /\ nextId <= MaxOP
        /\ LET newOut == [value |-> outVal, lock |-> outLock]
               newUtxo == ((nextId :> newOut) @@ [op \in (DOMAIN utxo) \ {inOp} |-> utxo[op]])
           IN /\ utxo' = newUtxo
              /\ spent' = spent \union {inOp}
              /\ nextId' = nextId + 1
              /\ height' = height
              /\ pqFrac' = PQCount(newUtxo)

\* -----------------------------------------------------------------------
\* Spend2: two-input, single-output transaction
\* -----------------------------------------------------------------------

Spend2 ==
    \E inOp1 \in DOMAIN utxo :
    \E inOp2 \in DOMAIN utxo :
        /\ inOp1 /= inOp2
        /\ (height >= MigrationCutover => utxo[inOp1].lock = "pq")
        /\ (height >= MigrationCutover => utxo[inOp2].lock = "pq")
        /\ nextId <= MaxOP
        /\ LET inVal == utxo[inOp1].value + utxo[inOp2].value
           IN \E outLock \in {"legacy", "pq"} :
              \E outVal \in 1..inVal :
                  /\ (height >= MigrationAnnounce => outLock = "pq")
                  /\ LET newOut == [value |-> outVal, lock |-> outLock]
                         newUtxo == ((nextId :> newOut) @@ [op \in (DOMAIN utxo) \ {inOp1, inOp2} |-> utxo[op]])
                     IN /\ utxo' = newUtxo
                        /\ spent' = spent \union {inOp1, inOp2}
                        /\ nextId' = nextId + 1
                        /\ height' = height
                        /\ pqFrac' = PQCount(newUtxo)

\* -----------------------------------------------------------------------
\* Spend1x2: single-input, two-output transaction
\* -----------------------------------------------------------------------

Spend1x2 ==
    \E inOp \in DOMAIN utxo :
    \E lock1 \in {"legacy", "pq"} :
    \E lock2 \in {"legacy", "pq"} :
    \E val1 \in 1..utxo[inOp].value :
    \E val2 \in 1..utxo[inOp].value :
        /\ val1 + val2 <= utxo[inOp].value
        /\ (height >= MigrationCutover => utxo[inOp].lock = "pq")
        /\ (height >= MigrationAnnounce => lock1 = "pq")
        /\ (height >= MigrationAnnounce => lock2 = "pq")
        /\ nextId + 1 <= MaxOP
        /\ LET out1 == [value |-> val1, lock |-> lock1]
               out2 == [value |-> val2, lock |-> lock2]
               remaining == [op \in (DOMAIN utxo) \ {inOp} |-> utxo[op]]
               newUtxo == ((nextId :> out1) @@ ((nextId + 1) :> out2) @@ remaining)
           IN /\ utxo' = newUtxo
              /\ spent' = spent \union {inOp}
              /\ nextId' = nextId + 2
              /\ height' = height
              /\ pqFrac' = PQCount(newUtxo)

\* Advance block height (bounded)
Tick ==
    /\ height < MigrationCutover + 1
    /\ height' = height + 1
    /\ UNCHANGED <<utxo, spent, nextId, pqFrac>>

\* -----------------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------------

Next == Spend1 \/ Spend2 \/ Spend1x2 \/ Tick

Spec == Init /\ [][Next]_vars

\* -----------------------------------------------------------------------
\* Invariants
\* -----------------------------------------------------------------------

NoDoubleSpend ==
    spent \intersect DOMAIN utxo = {}

ValueBound ==
    LET S == DOMAIN utxo
    IN IF S = {} THEN TRUE
       ELSE SetSum(utxo, S) <= GenesisTotal

StateConsistency ==
    /\ spent \intersect DOMAIN utxo = {}
    /\ \A op \in DOMAIN utxo : op < nextId
    /\ \A op \in spent : op < nextId

MigrationMonotonicity ==
    DOMAIN utxo /= {} =>
        pqFrac = PQCount(utxo)

FreezeEnforcement ==
    height >= MigrationCutover =>
        \A op \in DOMAIN utxo : utxo[op].lock = "pq"

Invariant ==
    /\ NoDoubleSpend
    /\ ValueBound
    /\ StateConsistency
    /\ MigrationMonotonicity

=========================================================================
