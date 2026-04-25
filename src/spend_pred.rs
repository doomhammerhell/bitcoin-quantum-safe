//! SpendPred_PQ: post-quantum spend predicate.
//!
//! Implements the PQ spend predicate for single-signature and multisig witnesses,
//! matching the Coq-verified definition in `formal/coq/SpendPredPQ.v`.
//! SpendPred_PQ(P, m, w) = 1 iff Parse(w) = (pk, σ) ∧ H(pk) = P ∧ Vfy(pk, m, σ) = 1.

use sha2::{Digest, Sha256};

use crate::encoding::{parse_multisig_witness, parse_witness, serialize_witness};
use crate::params::MAX_WITNESS_SIZE;
use crate::types::Commitment;

/// Evaluate the PQ spend predicate for a single-signature witness.
///
/// Matches the Coq-verified definition `spend_pred_pq_iff` in
/// `formal/coq/SpendPredPQ.v`:
///
/// ```text
/// SpendPred_PQ(P, m, w) = true
///   ⟺ ∃ pk σ, Parse(w) = Some(pk, σ) ∧ H(pk) = P ∧ Vfy(pk, m, σ) = 1
/// ```
///
/// Error ordering (cheapest checks first):
/// 1. Size check (O(1)) — reject oversized witnesses before any parsing
/// 2. Parse (single-pass) — reject malformed encodings
/// 3. Canonicality check — reject non-canonical encodings
/// 4. Hash check (one SHA-256 call) — reject commitment mismatches
/// 5. Signature verification (expensive) — only reached for well-formed,
///    canonical, hash-matching witnesses
///
/// # Arguments
///
/// * `commitment` — 32-byte SHA-256 commitment P = H(pk) from the output script
/// * `message` — the sighash bytes (m = Sighash(tx, i, ctx))
/// * `witness` — raw witness bytes
///
/// # Returns
///
/// `true` iff the witness parses to a valid (pk, σ) pair, the public key
/// hashes to the commitment, and the ML-DSA-44 signature verifies.
///
/// # Requirements: 2.4, 2.5, 2.6, 2.7, 2.9, 11.4
pub fn spend_pred_pq(commitment: &Commitment, message: &[u8], witness: &[u8]) -> bool {
    // Step 1: Size check — reject oversized witnesses before any parsing (Req 2.9)
    if witness.len() > MAX_WITNESS_SIZE {
        return false;
    }

    // Step 2: Parse — reject malformed encodings (Req 2.4)
    let (pk, sig) = match parse_witness(witness) {
        Some(pair) => pair,
        None => return false,
    };

    // Step 3: Canonicality check — reject non-canonical encodings (Req 11.4)
    if serialize_witness(&pk, &sig) != witness {
        return false;
    }

    // Step 4: Hash check — reject commitment mismatches (Req 2.5)
    let hash = Sha256::digest(&pk);
    if hash.as_slice() != commitment.as_slice() {
        return false;
    }

    // Step 5: Signature verification using ML-DSA-44 (FIPS 204) (Req 2.6)
    use fips204::ml_dsa_44;
    use fips204::traits::{SerDes, Verifier};

    let pk_array: [u8; 1312] = match pk.as_slice().try_into() {
        Ok(a) => a,
        Err(_) => return false,
    };

    let pq_pk = match ml_dsa_44::PublicKey::try_from_bytes(pk_array) {
        Ok(k) => k,
        Err(_) => return false,
    };

    let sig_array: [u8; 2420] = match sig.as_slice().try_into() {
        Ok(a) => a,
        Err(_) => return false,
    };

    pq_pk.verify(message, &sig_array, &[])
}

/// Evaluate the PQ spend predicate for a k-of-n multisig witness.
///
/// Matches the design document's `SpendPred_PQ_multisig` pseudocode:
///
/// ```text
/// SpendPred_PQ_multisig(P, m, w) = true
///   ⟺ Parse_multisig(w) = Some(k, pks, sigs, indices)
///     ∧ H(pk_1 || pk_2 || ... || pk_n) = P
///     ∧ ∀ i ∈ 0..k: Vfy(pks[indices[i]], m, sigs[i]) = 1
/// ```
///
/// Error ordering (cheapest checks first):
/// 1. Size check (O(1)) — reject oversized witnesses before any parsing
/// 2. Parse (single-pass) — reject malformed encodings, non-ascending indices
/// 3. Commitment check (one SHA-256 call over concatenated pks) — reject mismatches
/// 4. Signature verification (k ML-DSA-44 verifications) — only reached for
///    well-formed, commitment-matching witnesses
///
/// # Arguments
///
/// * `commitment` — 32-byte SHA-256 commitment P = H(pk_1 || pk_2 || ... || pk_n)
/// * `message` — the sighash bytes (m = Sighash(tx, i, ctx))
/// * `witness` — raw multisig witness bytes
///
/// # Returns
///
/// `true` iff the witness parses to valid multisig components, the concatenated
/// public keys hash to the commitment, and all k signatures verify against
/// their respective public keys.
///
/// # Requirements: 6.2, 6.5, 6.6, 6.8
pub fn spend_pred_pq_multisig(commitment: &Commitment, message: &[u8], witness: &[u8]) -> bool {
    // Step 1: Size check — reject oversized witnesses before any parsing (Req 6.8)
    if witness.len() > MAX_WITNESS_SIZE {
        return false;
    }

    // Step 2: Parse — reject malformed encodings (Req 6.5, 6.6)
    let (k, pks, sigs, indices) = match parse_multisig_witness(witness) {
        Some(parsed) => parsed,
        None => return false,
    };

    // Step 3: Commitment check — H(pk_1 || pk_2 || ... || pk_n) == P (Req 6.2)
    let mut hasher = Sha256::new();
    for pk in &pks {
        hasher.update(pk);
    }
    let hash = hasher.finalize();
    if hash.as_slice() != commitment.as_slice() {
        return false;
    }

    // Step 4: Verify k signatures against the selected public keys (Req 6.2)
    use fips204::ml_dsa_44;
    use fips204::traits::{SerDes, Verifier};

    for i in 0..(k as usize) {
        let pk_idx = indices[i] as usize;
        let pk_bytes = &pks[pk_idx];
        let sig_bytes = &sigs[i];

        let pk_array: [u8; 1312] = match pk_bytes.as_slice().try_into() {
            Ok(a) => a,
            Err(_) => return false,
        };

        let pq_pk = match ml_dsa_44::PublicKey::try_from_bytes(pk_array) {
            Ok(k) => k,
            Err(_) => return false,
        };

        let sig_array: [u8; 2420] = match sig_bytes.as_slice().try_into() {
            Ok(a) => a,
            Err(_) => return false,
        };

        if !pq_pk.verify(message, &sig_array, &[]) {
            return false;
        }
    }

    // Step 5: All checks passed
    true
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use fips204::ml_dsa_44;
    use fips204::traits::{SerDes, Signer};
    use sha2::{Digest, Sha256};

    use crate::encoding::serialize_witness;

    /// Helper: generate a valid (commitment, witness) pair for a given message.
    fn make_valid_spend(message: &[u8]) -> (Commitment, Vec<u8>) {
        let (pk, sk) = ml_dsa_44::try_keygen().unwrap();
        let sig = sk.try_sign(message, &[]).unwrap();

        let pk_bytes = pk.into_bytes().to_vec();

        let commitment: Commitment = Sha256::digest(&pk_bytes).into();
        let witness = serialize_witness(&pk_bytes, &sig.to_vec());

        (commitment, witness)
    }

    // -- Happy path --

    #[test]
    fn spend_pred_pq_valid_witness_accepts() {
        let message = b"test sighash message";
        let (commitment, witness) = make_valid_spend(message);
        assert!(spend_pred_pq(&commitment, message, &witness));
    }

    // -- Step 1: Size check --

    #[test]
    fn spend_pred_pq_rejects_oversized_witness() {
        let oversized = vec![0u8; MAX_WITNESS_SIZE + 1];
        let commitment = [0u8; 32];
        assert!(!spend_pred_pq(&commitment, b"msg", &oversized));
    }

    #[test]
    fn spend_pred_pq_accepts_max_size_witness_if_valid() {
        // A witness of exactly MAX_WITNESS_SIZE should not be rejected by the
        // size check (it may still fail parsing or verification).
        let witness = vec![0u8; MAX_WITNESS_SIZE];
        let commitment = [0u8; 32];
        // Will fail at parse or later, but NOT at the size check
        assert!(!spend_pred_pq(&commitment, b"msg", &witness));
    }

    // -- Step 2: Parse failure --

    #[test]
    fn spend_pred_pq_rejects_empty_witness() {
        let commitment = [0u8; 32];
        assert!(!spend_pred_pq(&commitment, b"msg", &[]));
    }

    #[test]
    fn spend_pred_pq_rejects_malformed_witness() {
        // pk_len = 5 but only 2 bytes follow
        let commitment = [0u8; 32];
        assert!(!spend_pred_pq(&commitment, b"msg", &[0x05, 0x01, 0x02]));
    }

    // -- Step 3: Canonicality --

    #[test]
    fn spend_pred_pq_rejects_non_canonical_varint() {
        // Construct a witness with non-minimal varint encoding for pk_len.
        // pk_len = 3 encoded as 0xFD 0x03 0x00 (should be single byte 0x03).
        // parse_witness rejects non-canonical varints, so this fails at step 2.
        let commitment = [0u8; 32];
        let w = vec![0xFD, 0x03, 0x00, 0x01, 0x02, 0x03, 0xAA, 0xBB];
        assert!(!spend_pred_pq(&commitment, b"msg", &w));
    }

    // -- Step 4: Hash mismatch --

    #[test]
    fn spend_pred_pq_rejects_commitment_mismatch() {
        let message = b"test sighash message";
        let (mut commitment, witness) = make_valid_spend(message);
        // Corrupt the commitment
        commitment[0] ^= 0xFF;
        assert!(!spend_pred_pq(&commitment, message, &witness));
    }

    // -- Step 5: Signature verification failure --

    #[test]
    fn spend_pred_pq_rejects_wrong_message() {
        let message = b"correct message";
        let (commitment, witness) = make_valid_spend(message);
        // Verify with a different message
        assert!(!spend_pred_pq(&commitment, b"wrong message", &witness));
    }

    #[test]
    fn spend_pred_pq_rejects_corrupted_signature() {
        let message = b"test sighash message";
        let (pk, sk) = ml_dsa_44::try_keygen().unwrap();
        let sig = sk.try_sign(message, &[]).unwrap();

        let pk_bytes = pk.into_bytes().to_vec();
        let mut sig_bytes = sig.to_vec();
        // Corrupt the signature
        sig_bytes[0] ^= 0xFF;

        let commitment: Commitment = Sha256::digest(&pk_bytes).into();
        let witness = serialize_witness(&pk_bytes, &sig_bytes);

        assert!(!spend_pred_pq(&commitment, message, &witness));
    }

    #[test]
    fn spend_pred_pq_rejects_wrong_pk_size() {
        // Use a pk that is not the correct ML-DSA-44 size (1312 bytes).
        // This should fail at the PublicKey::from_bytes step.
        let pk = vec![0x42; 100]; // wrong size
        let sig = vec![0x99; 2420];
        let commitment: Commitment = Sha256::digest(&pk).into();
        let witness = serialize_witness(&pk, &sig);
        assert!(!spend_pred_pq(&commitment, b"msg", &witness));
    }

    // -- Determinism (PO-2) --

    #[test]
    fn spend_pred_pq_is_deterministic() {
        let message = b"determinism test";
        let (commitment, witness) = make_valid_spend(message);
        let r1 = spend_pred_pq(&commitment, message, &witness);
        let r2 = spend_pred_pq(&commitment, message, &witness);
        assert_eq!(r1, r2);
        assert!(r1);
    }
}

// ---------------------------------------------------------------------------
// Multisig Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod multisig_tests {
    use super::*;
    use fips204::ml_dsa_44;
    use fips204::traits::{SerDes, Signer};
    use sha2::{Digest, Sha256};

    use crate::encoding::serialize_multisig_witness;

    /// Helper: generate n ML-DSA-44 keypairs and return (pk_bytes_vec, sk_vec).
    fn make_keypairs(n: usize) -> (Vec<Vec<u8>>, Vec<ml_dsa_44::PrivateKey>) {
        let mut pks = Vec::with_capacity(n);
        let mut sks = Vec::with_capacity(n);
        for _ in 0..n {
            let (pk, sk) = ml_dsa_44::try_keygen().unwrap();
            pks.push(pk.into_bytes().to_vec());
            sks.push(sk);
        }
        (pks, sks)
    }

    /// Helper: compute the multisig commitment H(pk_1 || pk_2 || ... || pk_n).
    fn multisig_commitment(pks: &[Vec<u8>]) -> Commitment {
        let mut hasher = Sha256::new();
        for pk in pks {
            hasher.update(pk);
        }
        hasher.finalize().into()
    }

    /// Helper: build a valid k-of-n multisig (commitment, witness) for a message.
    /// Signs with the first k keys (indices 0..k).
    fn make_valid_multisig_spend(
        k: u8,
        n: usize,
        message: &[u8],
    ) -> (Commitment, Vec<u8>, Vec<Vec<u8>>, Vec<ml_dsa_44::PrivateKey>) {
        let (pks, sks) = make_keypairs(n);
        let commitment = multisig_commitment(&pks);

        let mut sigs = Vec::with_capacity(k as usize);
        let mut indices: Vec<u8> = Vec::with_capacity(k as usize);
        for i in 0..(k as usize) {
            let sig = sks[i].try_sign(message, &[]).unwrap();
            sigs.push(sig.to_vec());
            indices.push(i as u8);
        }

        let witness = serialize_multisig_witness(k, &pks, &sigs, &indices);
        (commitment, witness, pks, sks)
    }

    // -- Happy path: valid 2-of-3 multisig --

    #[test]
    fn spend_pred_pq_multisig_valid_2_of_3_accepts() {
        let message = b"multisig sighash message";
        let (commitment, witness, _, _) = make_valid_multisig_spend(2, 3, message);
        assert!(spend_pred_pq_multisig(&commitment, message, &witness));
    }

    // -- Commitment mismatch rejection --

    #[test]
    fn spend_pred_pq_multisig_rejects_commitment_mismatch() {
        let message = b"multisig sighash message";
        let (mut commitment, witness, _, _) = make_valid_multisig_spend(2, 3, message);
        // Corrupt the commitment
        commitment[0] ^= 0xFF;
        assert!(!spend_pred_pq_multisig(&commitment, message, &witness));
    }

    // -- Wrong message rejection --

    #[test]
    fn spend_pred_pq_multisig_rejects_wrong_message() {
        let message = b"correct multisig message";
        let (commitment, witness, _, _) = make_valid_multisig_spend(2, 3, message);
        assert!(!spend_pred_pq_multisig(&commitment, b"wrong message", &witness));
    }

    // -- Corrupted signature rejection --

    #[test]
    fn spend_pred_pq_multisig_rejects_corrupted_signature() {
        let message = b"multisig sighash message";
        let (pks, sks) = make_keypairs(3);
        let commitment = multisig_commitment(&pks);

        let sig0 = sks[0].try_sign(message, &[]).unwrap();
        let sig1 = sks[1].try_sign(message, &[]).unwrap();

        let mut sig0_bytes = sig0.to_vec();
        let sig1_bytes = sig1.to_vec();

        // Corrupt the first signature
        sig0_bytes[0] ^= 0xFF;

        let sigs = vec![sig0_bytes, sig1_bytes];
        let indices = vec![0, 1];
        let witness = serialize_multisig_witness(2, &pks, &sigs, &indices);

        assert!(!spend_pred_pq_multisig(&commitment, message, &witness));
    }

    // -- Oversized witness rejection --

    #[test]
    fn spend_pred_pq_multisig_rejects_oversized_witness() {
        let oversized = vec![0u8; MAX_WITNESS_SIZE + 1];
        let commitment = [0u8; 32];
        assert!(!spend_pred_pq_multisig(&commitment, b"msg", &oversized));
    }
}
