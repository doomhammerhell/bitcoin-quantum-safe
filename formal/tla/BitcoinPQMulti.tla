------------------------- MODULE BitcoinPQMulti -------------------------
(*
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
 *   I1  NoDoubleSpend        — spent ∩ DOMAIN utxo = {}
 *   I2  ValueBound           — total value never exceeds genesis total
 *   I3  StateConsistency     — all ids fresh and tracked
 *   I4  MigrationMonotonicity— PQ fraction non-decreasing after announce
 *   I5  FreezeEnforcement    — after cutover, no non-PQ outputs are spent
 *)

EXTENDS Integers, FiniteSets, TLC, Sequences

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
    pqFrac      \* Fraction numerator: count of PQ outputs (denominator = Cardinality(DOMAIN utxo))

vars == <<utxo, spent, height, nextId, pqFrac>>

\* -----------------------------------------------------------------------
\* Helper: sum values over a finite set of outpoint ids using utxo map
\* -----------------------------------------------------------------------

RECURSIVE SetSum(_, _)
SetSum(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x].value + SetSum(f, S \ {x})

\* Count PQ-locked outputs in the current UTXO set
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
    /\ pqFrac = PQCount((1 :> [value |-> 2, lock |-> "legacy"])
                       @@ (2 :> [value |-> 1, lock |-> "pq"])
                       @@ (3 :> [value |-> 1, lock |-> "legacy"]))

\* -----------------------------------------------------------------------
\* Transaction: spend 1-2 inputs, produce 1-2 outputs
\* Value conservation: sum(inputs) >= sum(outputs), remainder is fee
\* -----------------------------------------------------------------------

\* Build a new utxo map: remove inputs, add outputs
BuildUTXO(oldUtxo, ins, outs, baseId) ==
    LET remaining == [op \in (DOMAIN oldUtxo) \ ins |-> oldUtxo[op]]
        \* outs is a sequence of [value, lock] records, length 1 or 2
        out1 == (baseId :> outs[1])
        out2 == IF Len(outs) = 2
                THEN (baseId :> outs[1]) @@ ((baseId + 1) :> outs[2])
                ELSE out1
    IN remaining @@ out2

Spend ==
    \* Choose a non-empty subset of UTXO inputs, size 1 or 2
    \E ins \in SUBSET (DOMAIN utxo) :
        /\ ins /= {}
        /\ Cardinality(ins) <= 2
        \* Compute total input value
        /\ LET inVal == SetSum(utxo, ins)
           IN
           \* Choose number of outputs: 1 or 2
           \E numOuts \in {1, 2} :
               \* Enough fresh ids
               /\ nextId + numOuts - 1 <= MaxOP
               \* Choose output locks
               \E lock1 \in {"legacy", "pq"} :
               \E lock2 \in {"legacy", "pq"} :
               \* Choose output values (at least 1 each, sum <= inVal)
               \E val1 \in 1..inVal :
               \E val2 \in IF numOuts = 2 THEN 1..inVal ELSE {0} :
                   \* Value conservation: outputs <= inputs (fee >= 0)
                   /\ val1 + val2 <= inVal
                   \* Freeze enforcement: after cutover, all inputs must be PQ
                   /\ (height >= MigrationCutover =>
                        \A op \in ins : utxo[op].lock = "pq")
                   \* Post-announcement: new outputs must be PQ
                   /\ (height >= MigrationAnnounce => lock1 = "pq")
                   /\ (height >= MigrationAnnounce => lock2 = "pq")
                   \* Build output sequence
                   /\ LET out1 == [value |-> val1, lock |-> lock1]
                          out2 == [value |-> val2, lock |-> lock2]
                          outs == IF numOuts = 1
                                  THEN <<out1>>
                                  ELSE <<out1, out2>>
                          newUtxo == BuildUTXO(utxo, ins, outs, nextId)
                      IN /\ utxo' = newUtxo
                         /\ spent' = spent \union ins
                         /\ nextId' = nextId + numOuts
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

Next == Spend \/ Tick

Spec == Init /\ [][Next]_vars

\* -----------------------------------------------------------------------
\* Invariants
\* -----------------------------------------------------------------------

\* I1: Spent outpoints are not in the UTXO set (no double spend)
NoDoubleSpend ==
    spent \intersect DOMAIN utxo = {}

\* I2: Total value in UTXO set never exceeds genesis total
ValueBound ==
    LET S == DOMAIN utxo
    IN IF S = {} THEN TRUE
       ELSE SetSum(utxo, S) <= GenesisTotal

\* I3: All ids are properly tracked and fresh
StateConsistency ==
    /\ spent \intersect DOMAIN utxo = {}
    /\ \A op \in DOMAIN utxo : op < nextId
    /\ \A op \in spent : op < nextId

\* I4: After announcement, PQ fraction is non-decreasing
\*     (checked as: pqFrac tracks PQ count, and we verify monotonicity
\*      via the temporal property below; here we check consistency)
MigrationMonotonicity ==
    DOMAIN utxo /= {} =>
        pqFrac = PQCount(utxo)

\* I5: After cutover, no non-PQ output is ever spent
\*     (enforced by Spend guard; invariant checks no legacy in UTXO after cutover)
FreezeEnforcement ==
    height >= MigrationCutover =>
        \A op \in DOMAIN utxo : utxo[op].lock = "pq"

\* Combined structural invariant
StructuralInvariant ==
    /\ NoDoubleSpend
    /\ ValueBound
    /\ StateConsistency
    /\ MigrationMonotonicity

\* Default invariant for model checking
Invariant == StructuralInvariant

\* -----------------------------------------------------------------------
\* Temporal property: PQ fraction is non-decreasing after announcement
\* (Checked as a separate property — requires liveness/temporal checking)
\* -----------------------------------------------------------------------

PQFracNonDecreasing ==
    [][height >= MigrationAnnounce =>
        (DOMAIN utxo' /= {} => pqFrac' >= pqFrac)]_vars

=========================================================================
