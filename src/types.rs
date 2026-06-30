//! Core types for the PQ witness protocol.
//!
//! Defines commitments, keys, signatures, transactions, UTXO set,
//! witness versions, and script type classification.
//!
//! The UTXO set is a finite partial function from outpoints to outputs
//! (Requirements 2.1, 2.2). The runtime representation is intentionally
//! hidden behind an extensional store contract.
//! Output script format: `<version_byte> <32-byte commitment>` where
//! commitment P = H(pk) using SHA-256.

#[cfg(not(kani))]
use std::collections::{hash_map, HashMap};
#[cfg(kani)]
use std::slice;

#[cfg(kani)]
const KANI_UTXO_CAPACITY: usize = 4;

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
/// Must be hashable for use as a runtime UTXO-store key.
/// Kani uses a deterministic finite-map model.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

/// Extensional contract for UTXO stores.
///
/// Consensus code must depend on these partial-function operations rather than
/// on the concrete runtime map. Two stores are equivalent for protocol
/// refinement when `canonical_entries` returns the same key-sorted snapshot.
pub trait UtxoStore {
    /// Insert or replace an output by outpoint.
    fn insert(&mut self, outpoint: OutPoint, output: Output) -> Option<Output>;

    /// Lookup an output by outpoint.
    fn get(&self, outpoint: &OutPoint) -> Option<&Output>;

    /// Remove an output by outpoint.
    fn remove(&mut self, outpoint: &OutPoint) -> Option<Output>;

    /// Return `true` iff `get(outpoint)` returns `Some(_)`.
    fn contains_key(&self, outpoint: &OutPoint) -> bool {
        self.get(outpoint).is_some()
    }

    /// Number of bindings in the finite store.
    fn len(&self) -> usize;

    /// Return `true` iff the finite store has no bindings.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Deterministic key-sorted snapshot for extensional comparison.
    fn canonical_entries(&self) -> Vec<(OutPoint, Output)>;
}

/// Runtime UTXO set: a finite partial function from outpoints to outputs.
///
/// The concrete representation is a `HashMap`, but callers intentionally see
/// only the partial-function API above. This keeps transition reasoning tied
/// to extensional map behavior rather than randomized hash-table internals.
#[cfg(not(kani))]
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct UtxoSet {
    entries: HashMap<OutPoint, Output>,
}

#[cfg(not(kani))]
impl UtxoSet {
    /// Create an empty runtime UTXO set.
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    /// Insert or replace an output by outpoint.
    pub fn insert(&mut self, outpoint: OutPoint, output: Output) -> Option<Output> {
        self.entries.insert(outpoint, output)
    }

    /// Lookup an output by outpoint.
    pub fn get(&self, outpoint: &OutPoint) -> Option<&Output> {
        self.entries.get(outpoint)
    }

    /// Remove an output by outpoint.
    pub fn remove(&mut self, outpoint: &OutPoint) -> Option<Output> {
        self.entries.remove(outpoint)
    }

    /// Check whether an outpoint is present.
    pub fn contains_key(&self, outpoint: &OutPoint) -> bool {
        self.entries.contains_key(outpoint)
    }

    /// Number of bindings in the finite store.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Return `true` iff the finite store has no bindings.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Iterate over stored outputs.
    pub fn values(&self) -> hash_map::Values<'_, OutPoint, Output> {
        self.entries.values()
    }

    /// Iterate over stored bindings. Iteration order is not consensus-significant.
    pub fn iter(&self) -> hash_map::Iter<'_, OutPoint, Output> {
        self.entries.iter()
    }

    /// Iterate over stored outpoints. Iteration order is not consensus-significant.
    pub fn keys(&self) -> hash_map::Keys<'_, OutPoint, Output> {
        self.entries.keys()
    }

    /// Deterministic key-sorted snapshot for extensional comparison.
    pub fn canonical_entries(&self) -> Vec<(OutPoint, Output)> {
        let mut entries: Vec<(OutPoint, Output)> = self
            .entries
            .iter()
            .map(|(outpoint, output)| (outpoint.clone(), output.clone()))
            .collect();
        entries.sort_by(|(left, _), (right, _)| left.cmp(right));
        entries
    }
}

#[cfg(not(kani))]
impl<'a> IntoIterator for &'a UtxoSet {
    type Item = (&'a OutPoint, &'a Output);
    type IntoIter = hash_map::Iter<'a, OutPoint, Output>;

    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter()
    }
}

#[cfg(not(kani))]
impl From<HashMap<OutPoint, Output>> for UtxoSet {
    fn from(entries: HashMap<OutPoint, Output>) -> Self {
        Self { entries }
    }
}

#[cfg(not(kani))]
impl UtxoStore for UtxoSet {
    fn insert(&mut self, outpoint: OutPoint, output: Output) -> Option<Output> {
        UtxoSet::insert(self, outpoint, output)
    }

    fn get(&self, outpoint: &OutPoint) -> Option<&Output> {
        UtxoSet::get(self, outpoint)
    }

    fn remove(&mut self, outpoint: &OutPoint) -> Option<Output> {
        UtxoSet::remove(self, outpoint)
    }

    fn contains_key(&self, outpoint: &OutPoint) -> bool {
        UtxoSet::contains_key(self, outpoint)
    }

    fn len(&self) -> usize {
        UtxoSet::len(self)
    }

    fn is_empty(&self) -> bool {
        UtxoSet::is_empty(self)
    }

    fn canonical_entries(&self) -> Vec<(OutPoint, Output)> {
        UtxoSet::canonical_entries(self)
    }
}

/// Deterministic finite map used only by Kani to avoid verifier-unsupported OS
/// randomness and standard-library map internals from `HashMap`'s `RandomState`.
#[cfg(kani)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UtxoSet {
    entries: [Option<(OutPoint, Output)>; KANI_UTXO_CAPACITY],
}

#[cfg(kani)]
impl UtxoSet {
    /// Create an empty Kani finite map.
    pub fn new() -> Self {
        Self {
            entries: [None, None, None, None],
        }
    }

    /// Insert or replace an output by outpoint, matching `HashMap::insert`
    /// extensionally for the verifier's bounded finite-map model.
    pub fn insert(&mut self, outpoint: OutPoint, output: Output) -> Option<Output> {
        for entry in &mut self.entries {
            if let Some((existing_outpoint, existing_output)) = entry {
                if *existing_outpoint == outpoint {
                    return Some(std::mem::replace(existing_output, output));
                }
            }
        }
        for entry in &mut self.entries {
            if entry.is_none() {
                *entry = Some((outpoint, output));
                return None;
            }
        }
        unreachable!()
    }

    /// Lookup an output by outpoint.
    pub fn get(&self, outpoint: &OutPoint) -> Option<&Output> {
        for entry in &self.entries {
            if let Some((existing_outpoint, output)) = entry {
                if existing_outpoint == outpoint {
                    return Some(output);
                }
            }
        }
        None
    }

    /// Remove an output by outpoint.
    pub fn remove(&mut self, outpoint: &OutPoint) -> Option<Output> {
        for entry in &mut self.entries {
            if entry
                .as_ref()
                .map(|(existing_outpoint, _)| existing_outpoint == outpoint)
                .unwrap_or(false)
            {
                return entry.take().map(|(_, output)| output);
            }
        }
        None
    }

    /// Check whether an outpoint is present.
    pub fn contains_key(&self, outpoint: &OutPoint) -> bool {
        self.get(outpoint).is_some()
    }

    /// Number of bindings in the finite store.
    pub fn len(&self) -> usize {
        self.entries.iter().filter(|entry| entry.is_some()).count()
    }

    /// Return `true` iff the finite store has no bindings.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Iterate over stored outputs.
    pub fn values(&self) -> UtxoValues<'_> {
        UtxoValues {
            iter: self.entries.iter(),
        }
    }

    /// Deterministic key-sorted snapshot for extensional comparison.
    pub fn canonical_entries(&self) -> Vec<(OutPoint, Output)> {
        let mut entries = Vec::new();
        for entry in &self.entries {
            if let Some((outpoint, output)) = entry {
                entries.push((outpoint.clone(), output.clone()));
            }
        }
        entries.sort_by(|(left, _), (right, _)| left.cmp(right));
        entries
    }
}

#[cfg(kani)]
impl Default for UtxoSet {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(kani)]
impl UtxoStore for UtxoSet {
    fn insert(&mut self, outpoint: OutPoint, output: Output) -> Option<Output> {
        UtxoSet::insert(self, outpoint, output)
    }

    fn get(&self, outpoint: &OutPoint) -> Option<&Output> {
        UtxoSet::get(self, outpoint)
    }

    fn remove(&mut self, outpoint: &OutPoint) -> Option<Output> {
        UtxoSet::remove(self, outpoint)
    }

    fn contains_key(&self, outpoint: &OutPoint) -> bool {
        UtxoSet::contains_key(self, outpoint)
    }

    fn len(&self) -> usize {
        UtxoSet::len(self)
    }

    fn is_empty(&self) -> bool {
        UtxoSet::is_empty(self)
    }

    fn canonical_entries(&self) -> Vec<(OutPoint, Output)> {
        UtxoSet::canonical_entries(self)
    }
}

/// Iterator over Kani finite-map values.
#[cfg(kani)]
pub struct UtxoValues<'a> {
    iter: slice::Iter<'a, Option<(OutPoint, Output)>>,
}

#[cfg(kani)]
impl<'a> Iterator for UtxoValues<'a> {
    type Item = &'a Output;

    fn next(&mut self) -> Option<Self::Item> {
        for entry in self.iter.by_ref() {
            if let Some((_, output)) = entry {
                return Some(output);
            }
        }
        None
    }
}

/// Return a deterministic, key-sorted snapshot of a UTXO set.
///
/// Runtime UTXO storage has intentionally unspecified iteration order.
/// Refinement and certificate generators use this helper to compare map
/// behavior extensionally, independent of hash table bucket order or randomized
/// hash seeding.
#[cfg(not(kani))]
pub fn canonical_utxo_entries(utxo: &UtxoSet) -> Vec<(OutPoint, Output)> {
    utxo.canonical_entries()
}

/// Return a deterministic, key-sorted snapshot of a Kani finite-map UTXO set.
#[cfg(kani)]
pub fn canonical_utxo_entries(utxo: &UtxoSet) -> Vec<(OutPoint, Output)> {
    utxo.canonical_entries()
}

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
        // OutPoint must be usable as a runtime UTXO-store key.
        let mut utxo_set = UtxoSet::new();
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
    fn canonical_utxo_entries_are_key_sorted() {
        let mut utxo_set = UtxoSet::new();
        let high = OutPoint {
            txid: [2u8; 32],
            vout: 0,
        };
        let low = OutPoint {
            txid: [1u8; 32],
            vout: 1,
        };
        let output = Output {
            script_version: 2,
            commitment: [0xAB; 32],
            value: 50_000,
        };

        utxo_set.insert(high.clone(), output.clone());
        utxo_set.insert(low.clone(), output);

        let snapshot = canonical_utxo_entries(&utxo_set);
        assert_eq!(snapshot.len(), 2);
        assert_eq!(snapshot[0].0, low);
        assert_eq!(snapshot[1].0, high);
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
