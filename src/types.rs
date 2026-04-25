//! Core types for the PQ witness protocol.
//!
//! Defines commitments, keys, signatures, transactions, UTXO set,
//! witness versions, and script type classification.
//!
//! The UTXO set is a finite partial function from outpoints to outputs
//! (Requirements 2.1, 2.2). OutPoint is hashable for HashMap usage.
//! Output script format: `<version_byte> <32-byte commitment>` where
//! commitment P = H(pk) using SHA-256.

use std::collections::HashMap;

// ---------------------------------------------------------------------------
// Primitive type aliases
// ---------------------------------------------------------------------------

/// Raw byte vector used throughout the protocol.
pub type Bytes = Vec<u8>;

/// 32-byte SHA-256 commitment: P = H(pk).
pub type Commitment = [u8; 32];

/// Public key bytes (variable length depending on scheme).
pub type PubKey = Vec<u8>;

/// Signature bytes (variable length depending on scheme).
pub type Signature = Vec<u8>;

/// Raw witness bytes as they appear on the wire.
pub type Witness = Vec<u8>;

// ---------------------------------------------------------------------------
// Transaction graph types
// ---------------------------------------------------------------------------

/// Reference to a specific output of a previous transaction.
///
/// Must be hashable for use as a key in `UtxoSet` (`HashMap<OutPoint, Output>`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OutPoint {
    /// Transaction id (hash of the transaction that created the output).
    pub txid: [u8; 32],
    /// Index of the output within that transaction.
    pub vout: u32,
}

/// A transaction output as stored in the UTXO set.
///
/// The output script is represented by a witness version byte and a 32-byte
/// commitment (`<version_byte> <32-byte commitment>`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Output {
    /// Witness/script version byte (0 = SegWit v0, 1 = Taproot, 2 = PQ, …).
    pub script_version: u8,
    /// 32-byte commitment (P = H(pk) for PQ outputs).
    pub commitment: Commitment,
    /// Value in satoshis.
    pub value: u64,
}

/// A transaction input: a reference to a previous output plus a witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TxInput {
    /// The outpoint being spent.
    pub outpoint: OutPoint,
    /// The witness data authorizing the spend.
    pub witness: Witness,
}

/// A transaction output as it appears inside a transaction body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TxOutput {
    /// Witness/script version byte.
    pub script_version: u8,
    /// 32-byte commitment.
    pub commitment: Commitment,
    /// Value in satoshis.
    pub value: u64,
}

/// A Bitcoin transaction (simplified for the PQ witness protocol model).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transaction {
    /// Transaction format version.
    pub version: u32,
    /// Transaction inputs.
    pub inputs: Vec<TxInput>,
    /// Transaction outputs.
    pub outputs: Vec<TxOutput>,
    /// Lock time (block height or unix timestamp).
    pub locktime: u32,
}

// ---------------------------------------------------------------------------
// Block and UTXO set
// ---------------------------------------------------------------------------

/// A block is a vector of transactions.
pub type Block = Vec<Transaction>;

/// The UTXO set: a finite partial function from outpoints to outputs.
pub type UtxoSet = HashMap<OutPoint, Output>;

// ---------------------------------------------------------------------------
// Witness and script classification enums
// ---------------------------------------------------------------------------

/// Witness version discriminant.
///
/// Maps the version byte in the output script to a semantic category.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WitnessVersion {
    /// SegWit v0 (P2WPKH / P2WSH).
    V0,
    /// SegWit v1 (Taproot).
    V1,
    /// SegWit v2 — post-quantum witness.
    V2Pq,
}

/// Classification of output script types for migration rule enforcement.
///
/// Used by the `Migration_Controller` to decide whether an output is legacy
/// or PQ-locked (Requirements 4.3, 5.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScriptType {
    /// Pay-to-Public-Key-Hash (legacy).
    P2PKH,
    /// Pay-to-Witness-Public-Key-Hash (SegWit v0).
    P2WPKH,
    /// Pay-to-Script-Hash (legacy wrapped).
    P2SH,
    /// Pay-to-Witness-Script-Hash (SegWit v0).
    P2WSH,
    /// Pay-to-Taproot (SegWit v1, secp256k1 key-path).
    P2TR,
    /// Pay-to-Post-Quantum (SegWit v2).
    P2PQ,
}

impl ScriptType {
    /// Returns `true` for all non-PQ (legacy) script types.
    ///
    /// Legacy types are subject to migration restrictions after the
    /// announcement height H_a and become frozen at cutover H_c.
    pub fn is_legacy(&self) -> bool {
        !matches!(self, ScriptType::P2PQ)
    }
}

// ---------------------------------------------------------------------------
// Convenience conversions
// ---------------------------------------------------------------------------

impl From<&Output> for ScriptType {
    /// Classify an output by its script version byte.
    ///
    /// Version 2 → `P2PQ`; version 1 → `P2TR`; version 0 → `P2WPKH`
    /// (simplified — real classification would inspect the full script).
    /// All other versions default to `P2PKH` as a conservative legacy bucket.
    fn from(output: &Output) -> Self {
        match output.script_version {
            0 => ScriptType::P2WPKH,
            1 => ScriptType::P2TR,
            2 => ScriptType::P2PQ,
            _ => ScriptType::P2PKH,
        }
    }
}

impl From<&TxOutput> for ScriptType {
    /// Classify a transaction output by its script version byte.
    fn from(output: &TxOutput) -> Self {
        match output.script_version {
            0 => ScriptType::P2WPKH,
            1 => ScriptType::P2TR,
            2 => ScriptType::P2PQ,
            _ => ScriptType::P2PKH,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn script_type_is_legacy() {
        assert!(ScriptType::P2PKH.is_legacy());
        assert!(ScriptType::P2WPKH.is_legacy());
        assert!(ScriptType::P2SH.is_legacy());
        assert!(ScriptType::P2WSH.is_legacy());
        assert!(ScriptType::P2TR.is_legacy());
        assert!(!ScriptType::P2PQ.is_legacy());
    }

    #[test]
    fn outpoint_is_hashable() {
        // OutPoint must be usable as a HashMap key (UtxoSet).
        let mut utxo_set: UtxoSet = HashMap::new();
        let op = OutPoint {
            txid: [0u8; 32],
            vout: 0,
        };
        let output = Output {
            script_version: 2,
            commitment: [0xAB; 32],
            value: 50_000,
        };
        utxo_set.insert(op.clone(), output.clone());
        assert_eq!(utxo_set.get(&op), Some(&output));
    }

    #[test]
    fn output_classification_from_version() {
        let pq = Output {
            script_version: 2,
            commitment: [0; 32],
            value: 0,
        };
        assert_eq!(ScriptType::from(&pq), ScriptType::P2PQ);
        assert!(!ScriptType::from(&pq).is_legacy());

        let taproot = Output {
            script_version: 1,
            commitment: [0; 32],
            value: 0,
        };
        assert_eq!(ScriptType::from(&taproot), ScriptType::P2TR);
        assert!(ScriptType::from(&taproot).is_legacy());

        let segwit_v0 = Output {
            script_version: 0,
            commitment: [0; 32],
            value: 0,
        };
        assert_eq!(ScriptType::from(&segwit_v0), ScriptType::P2WPKH);
        assert!(ScriptType::from(&segwit_v0).is_legacy());
    }

    #[test]
    fn tx_output_classification_from_version() {
        let pq = TxOutput {
            script_version: 2,
            commitment: [0; 32],
            value: 0,
        };
        assert_eq!(ScriptType::from(&pq), ScriptType::P2PQ);

        let legacy = TxOutput {
            script_version: 0,
            commitment: [0; 32],
            value: 0,
        };
        assert_eq!(ScriptType::from(&legacy), ScriptType::P2WPKH);
    }

    #[test]
    fn transaction_construction() {
        let tx = Transaction {
            version: 2,
            inputs: vec![TxInput {
                outpoint: OutPoint {
                    txid: [1u8; 32],
                    vout: 0,
                },
                witness: vec![0xDE, 0xAD],
            }],
            outputs: vec![TxOutput {
                script_version: 2,
                commitment: [0xBE; 32],
                value: 100_000,
            }],
            locktime: 0,
        };
        assert_eq!(tx.version, 2);
        assert_eq!(tx.inputs.len(), 1);
        assert_eq!(tx.outputs.len(), 1);
        assert_eq!(tx.locktime, 0);
    }

    #[test]
    fn witness_version_enum_variants() {
        assert_ne!(WitnessVersion::V0, WitnessVersion::V1);
        assert_ne!(WitnessVersion::V1, WitnessVersion::V2Pq);
        assert_eq!(WitnessVersion::V2Pq, WitnessVersion::V2Pq);
    }

    #[test]
    fn block_is_vec_of_transactions() {
        let block: Block = vec![
            Transaction {
                version: 2,
                inputs: vec![],
                outputs: vec![],
                locktime: 0,
            },
            Transaction {
                version: 2,
                inputs: vec![],
                outputs: vec![],
                locktime: 100,
            },
        ];
        assert_eq!(block.len(), 2);
    }
}
