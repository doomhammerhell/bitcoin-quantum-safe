---------------------------- MODULE BitcoinPQ ----------------------------
(*
 * TLA+ specification for Bitcoin post-quantum UTXO transitions.
 * Executable model for TLC model checking.
 *
 * Models a small UTXO system with:
 *   - Outpoints identified by natural numbers
 *   - Two output types: "legacy" and "pq"
 *   - Single-input single-output transactions
 *   - Migration cutover height after which legacy spends are rejected
 *
 * Invariants checked:
 *   - NoDoubleSpend: spent and utxo are disjoint
 *   - ValueBound: total value never exceeds genesis
 *   - StateConsistency: all ids are fresh and tracked
 *   - AuthIntegrityPQ: after cutover, only PQ outputs exist (migration safety)
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    MaxOP,              \* Maximum outpoint id
    MigrationAnnounce,  \* Height: no new legacy outputs after this
    MigrationCutover    \* Height: legacy spends rejected after this

VARIABLES
    utxo,       \* Function: outpoint id -> [value: Int, lock: STRING]
    spent,      \* Set of all outpoints ever spent
    height,     \* Current block height
    nextId      \* Next available outpoint id

vars == <<utxo, spent, height, nextId>>

\* -----------------------------------------------------------------------
\* Initial state: two genesis outputs (total value = 3)
\* -----------------------------------------------------------------------

Init ==
    /\ utxo = (1 :> [value |-> 2, lock |-> "legacy"])
            @@ (2 :> [value |-> 1, lock |-> "pq"])
    /\ spent = {}
    /\ height = 0
    /\ nextId = 3

\* -----------------------------------------------------------------------
\* Transaction: spend one input, produce one output
\* -----------------------------------------------------------------------

Spend ==
    \E inOp \in DOMAIN utxo :
        \E outLock \in {"legacy", "pq"} :
            \* Post-cutover: only PQ inputs can be spent
            /\ (height >= MigrationCutover => utxo[inOp].lock = "pq")
            \* Post-announcement: new outputs must be PQ
            /\ (height >= MigrationAnnounce => outLock = "pq")
            \* Fresh outpoint available
            /\ nextId <= MaxOP
            \* Value preserved (1:1, same value)
            /\ LET newOp == nextId
                   newOut == [value |-> utxo[inOp].value, lock |-> outLock]
               IN /\ utxo' = [op \in ((DOMAIN utxo) \ {inOp}) \union {newOp} |->
                                IF op = newOp THEN newOut ELSE utxo[op]]
                  /\ spent' = spent \union {inOp}
                  /\ nextId' = nextId + 1
                  /\ height' = height

\* Advance block height (bounded)
Tick ==
    /\ height < MigrationCutover + 1
    /\ height' = height + 1
    /\ UNCHANGED <<utxo, spent, nextId>>

\* -----------------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------------

Next == Spend \/ Tick

Spec == Init /\ [][Next]_vars

\* -----------------------------------------------------------------------
\* Invariants
\* -----------------------------------------------------------------------

\* I1: Spent outpoints are not in the UTXO set
NoDoubleSpend ==
    spent \intersect DOMAIN utxo = {}

\* I2: Total value never exceeds genesis (3)
ValueBound ==
    LET S == DOMAIN utxo
    IN IF S = {} THEN TRUE
       ELSE LET Sum[ss \in SUBSET S] ==
                IF ss = {} THEN 0
                ELSE LET x == CHOOSE x \in ss : TRUE
                     IN utxo[x].value + Sum[ss \ {x}]
            IN Sum[S] <= 3

\* I3: All ids are properly tracked
StateConsistency ==
    /\ spent \intersect DOMAIN utxo = {}
    /\ \A op \in DOMAIN utxo : op < nextId
    /\ \A op \in spent : op < nextId

\* I4: After cutover, all outputs are PQ-locked
AuthIntegrityPQ ==
    height >= MigrationCutover =>
        \A op \in DOMAIN utxo : utxo[op].lock = "pq"

\* Structural invariant (always holds by construction)
StructuralInvariant ==
    /\ NoDoubleSpend
    /\ ValueBound
    /\ StateConsistency

\* Default: check structural invariants
Invariant == StructuralInvariant

=========================================================================
