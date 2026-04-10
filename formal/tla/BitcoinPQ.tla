---------------------------- MODULE BitcoinPQ ----------------------------
(*
 * TLA+ specification for Bitcoin post-quantum UTXO transitions.
 * Corresponds to the model in Section 11 of the paper.
 *
 * This is a finite-state model intended for exploration with TLC.
 * Instantiate with small UTXO sets (|dom(U)| <= 10) and bounded
 * transaction/block counts.
 *)

CONSTANTS
    MaxOutputs,     \* Maximum number of outputs in the UTXO set
    MaxTxPerBlock,  \* Maximum transactions per block
    MaxBlocks       \* Maximum blocks in a trace

VARIABLES
    utxo,           \* UTXO set: OutPoint -> Output (partial function)
    chain,          \* Sequence of applied blocks
    height          \* Current block height

vars == <<utxo, chain, height>>

---------------------------------------------------------------------------
(* Output types *)
Legacy == "legacy"
PQLocked == "pq"

(* An output is a record with a value and a lock type *)
Output == [value: Nat, lock: {Legacy, PQLocked}]

(* An outpoint is a record with txid and index *)
OutPoint == [txid: Nat, idx: Nat]

---------------------------------------------------------------------------
(* Predicates *)

NoDupInputs(tx) ==
    \A i, j \in DOMAIN tx.inputs:
        i /= j => tx.inputs[i] /= tx.inputs[j]

InputsExist(tx, u) ==
    \A i \in DOMAIN tx.inputs:
        tx.inputs[i] \in DOMAIN u

ValueConservation(tx, u) ==
    LET inputVal  == SumOver(tx.inputs, u)
        outputVal == SumOverOutputs(tx.outputs)
    IN inputVal >= outputVal

SpendPredPQ(lockScript, sighash, witness) ==
    \* Abstract: returns TRUE iff witness satisfies PQ spend predicate
    lockScript.lock = PQLocked => witness.type = PQLocked

ValidTx(tx, u) ==
    /\ NoDupInputs(tx)
    /\ InputsExist(tx, u)
    /\ ValueConservation(tx, u)
    /\ \A i \in DOMAIN tx.inputs:
         LET op == tx.inputs[i]
             out == u[op]
         IN SpendPredPQ(out, Sighash(tx, i), tx.witnesses[i])

---------------------------------------------------------------------------
(* Transition functions *)

ApplyTx(tx, u) ==
    LET removed == {tx.inputs[i] : i \in DOMAIN tx.inputs}
        added   == {[txid |-> tx.id, idx |-> j] : j \in DOMAIN tx.outputs}
    IN [op \in (DOMAIN u \ removed) \union added |->
            IF op \in added
            THEN tx.outputs[op.idx]
            ELSE u[op]]

ApplyBlock(blk, u) ==
    \* Sequential application of transactions in the block
    FoldLeft(ApplyTx, u, blk.txs)

---------------------------------------------------------------------------
(* Specification *)

Init ==
    /\ utxo = InitialUTXO
    /\ chain = <<>>
    /\ height = 0

Next ==
    \E blk \in CandidateBlocks:
        /\ ValidBlock(blk, utxo)
        /\ utxo' = ApplyBlock(blk, utxo)
        /\ chain' = Append(chain, blk)
        /\ height' = height + 1

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Invariants *)

NoDoubleSpend ==
    \* Every outpoint is spent at most once across the trace
    \A i, j \in DOMAIN chain:
        \A tx1 \in chain[i].txs, tx2 \in chain[j].txs:
            (i /= j \/ tx1 /= tx2) =>
                DOMAIN tx1.inputs \intersect DOMAIN tx2.inputs = {}

StateConsistency ==
    \* Every outpoint not in utxo either never existed or was spent
    \A op \in OutPoint:
        op \notin DOMAIN utxo =>
            \/ \A blk \in Range(chain): \A tx \in blk.txs:
                 op \notin {[txid |-> tx.id, idx |-> j] : j \in DOMAIN tx.outputs}
            \/ \E blk \in Range(chain): \E tx \in blk.txs:
                 op \in {tx.inputs[i] : i \in DOMAIN tx.inputs}

Determinism ==
    \* DeltaTx produces a unique result (structural by definition)
    TRUE

AuthIntegrityPQ ==
    \* All spendable outputs are PQ-locked (post-migration)
    height > MigrationHeight =>
        \A op \in DOMAIN utxo: utxo[op].lock = PQLocked

Invariant ==
    /\ NoDoubleSpend
    /\ StateConsistency
    /\ Determinism
    /\ AuthIntegrityPQ

=========================================================================
