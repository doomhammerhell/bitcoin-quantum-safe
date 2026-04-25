//! Varint encoding and witness serialization/parsing.
//!
//! Implements Bitcoin compact-size varint encoding, single-signature witness
//! Serialize/Parse (matching the Coq-verified definition), and multisig
//! witness Serialize/Parse with canonical ordering constraints.

// ---------------------------------------------------------------------------
// Bitcoin compact-size varint encoding
// ---------------------------------------------------------------------------

/// Encode a `u64` value using Bitcoin's compact-size (varint) encoding.
///
/// Encoding rules:
/// - `0..=252`: single byte
/// - `253..=65_535`: `0xFD` prefix + 2 bytes little-endian
/// - `65_536..=4_294_967_295`: `0xFE` prefix + 4 bytes little-endian
/// - `4_294_967_296..`: `0xFF` prefix + 8 bytes little-endian
///
/// The encoding is always canonical (minimal): the smallest representation
/// that can hold the value is used.
pub fn encode_varint(value: u64) -> Vec<u8> {
    if value <= 252 {
        vec![value as u8]
    } else if value <= 0xFFFF {
        let mut buf = Vec::with_capacity(3);
        buf.push(0xFD);
        buf.extend_from_slice(&(value as u16).to_le_bytes());
        buf
    } else if value <= 0xFFFF_FFFF {
        let mut buf = Vec::with_capacity(5);
        buf.push(0xFE);
        buf.extend_from_slice(&(value as u32).to_le_bytes());
        buf
    } else {
        let mut buf = Vec::with_capacity(9);
        buf.push(0xFF);
        buf.extend_from_slice(&value.to_le_bytes());
        buf
    }
}

/// Decode a Bitcoin compact-size varint from the start of `data`.
///
/// Returns `Some((value, bytes_consumed))` on success, or `None` if:
/// - `data` is empty
/// - `data` is too short for the indicated encoding
/// - The encoding is non-canonical (non-minimal): e.g. using `0xFD` prefix
///   for a value that fits in a single byte
///
/// # Canonical encoding enforcement
///
/// A varint is canonical iff the prefix used is the smallest that can
/// represent the value. Specifically:
/// - `0xFD` prefix is only valid for values `253..=65_535`
/// - `0xFE` prefix is only valid for values `65_536..=4_294_967_295`
/// - `0xFF` prefix is only valid for values `>= 4_294_967_296`
///
/// Non-canonical encodings are rejected to prevent transaction malleability
/// (Requirement 11.4).
pub fn decode_varint(data: &[u8]) -> Option<(u64, usize)> {
    let first = *data.first()?;

    match first {
        0..=0xFC => Some((first as u64, 1)),

        0xFD => {
            if data.len() < 3 {
                return None;
            }
            let value = u16::from_le_bytes([data[1], data[2]]) as u64;
            // Canonical check: value must require the 0xFD prefix (>= 253).
            if value < 253 {
                return None;
            }
            Some((value, 3))
        }

        0xFE => {
            if data.len() < 5 {
                return None;
            }
            let value =
                u32::from_le_bytes([data[1], data[2], data[3], data[4]]) as u64;
            // Canonical check: value must require the 0xFE prefix (>= 65_536).
            if value < 0x1_0000 {
                return None;
            }
            Some((value, 5))
        }

        0xFF => {
            if data.len() < 9 {
                return None;
            }
            let value = u64::from_le_bytes([
                data[1], data[2], data[3], data[4], data[5], data[6], data[7],
                data[8],
            ]);
            // Canonical check: value must require the 0xFF prefix (>= 2^32).
            if value < 0x1_0000_0000 {
                return None;
            }
            Some((value, 9))
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- encode_varint --

    #[test]
    fn encode_varint_zero() {
        assert_eq!(encode_varint(0), vec![0x00]);
    }

    #[test]
    fn encode_varint_single_byte_max() {
        assert_eq!(encode_varint(252), vec![0xFC]);
    }

    #[test]
    fn encode_varint_fd_prefix_min() {
        // 253 → 0xFD 0xFD 0x00
        let encoded = encode_varint(253);
        assert_eq!(encoded, vec![0xFD, 0xFD, 0x00]);
    }

    #[test]
    fn encode_varint_fd_prefix_256() {
        // 256 → 0xFD 0x00 0x01
        let encoded = encode_varint(256);
        assert_eq!(encoded, vec![0xFD, 0x00, 0x01]);
    }

    #[test]
    fn encode_varint_fd_prefix_max() {
        // 65535 → 0xFD 0xFF 0xFF
        let encoded = encode_varint(65535);
        assert_eq!(encoded, vec![0xFD, 0xFF, 0xFF]);
    }

    #[test]
    fn encode_varint_fe_prefix_min() {
        // 65536 → 0xFE 0x00 0x00 0x01 0x00
        let encoded = encode_varint(65536);
        assert_eq!(encoded, vec![0xFE, 0x00, 0x00, 0x01, 0x00]);
    }

    #[test]
    fn encode_varint_fe_prefix_max() {
        // 4_294_967_295 (u32::MAX) → 0xFE 0xFF 0xFF 0xFF 0xFF
        let encoded = encode_varint(0xFFFF_FFFF);
        assert_eq!(encoded, vec![0xFE, 0xFF, 0xFF, 0xFF, 0xFF]);
    }

    #[test]
    fn encode_varint_ff_prefix_min() {
        // 4_294_967_296 → 0xFF followed by 8 LE bytes
        let encoded = encode_varint(0x1_0000_0000);
        assert_eq!(
            encoded,
            vec![0xFF, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00]
        );
    }

    #[test]
    fn encode_varint_ff_prefix_large() {
        let encoded = encode_varint(u64::MAX);
        assert_eq!(
            encoded,
            vec![0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]
        );
    }

    // -- decode_varint --

    #[test]
    fn decode_varint_empty() {
        assert_eq!(decode_varint(&[]), None);
    }

    #[test]
    fn decode_varint_zero() {
        assert_eq!(decode_varint(&[0x00]), Some((0, 1)));
    }

    #[test]
    fn decode_varint_single_byte_max() {
        assert_eq!(decode_varint(&[0xFC]), Some((252, 1)));
    }

    #[test]
    fn decode_varint_fd_prefix_valid() {
        // 256 encoded as 0xFD 0x00 0x01
        assert_eq!(decode_varint(&[0xFD, 0x00, 0x01]), Some((256, 3)));
    }

    #[test]
    fn decode_varint_fd_prefix_min_valid() {
        // 253 encoded as 0xFD 0xFD 0x00
        assert_eq!(decode_varint(&[0xFD, 0xFD, 0x00]), Some((253, 3)));
    }

    #[test]
    fn decode_varint_fe_prefix_valid() {
        assert_eq!(
            decode_varint(&[0xFE, 0x00, 0x00, 0x01, 0x00]),
            Some((65536, 5))
        );
    }

    #[test]
    fn decode_varint_ff_prefix_valid() {
        assert_eq!(
            decode_varint(&[0xFF, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00]),
            Some((0x1_0000_0000, 9))
        );
    }

    // -- canonical encoding rejection --

    #[test]
    fn decode_varint_rejects_non_canonical_fd_for_value_252() {
        // 252 encoded with 0xFD prefix: 0xFD 0xFC 0x00 — non-canonical
        assert_eq!(decode_varint(&[0xFD, 0xFC, 0x00]), None);
    }

    #[test]
    fn decode_varint_rejects_non_canonical_fd_for_value_0() {
        // 0 encoded with 0xFD prefix: 0xFD 0x00 0x00 — non-canonical
        assert_eq!(decode_varint(&[0xFD, 0x00, 0x00]), None);
    }

    #[test]
    fn decode_varint_rejects_non_canonical_fd_for_value_1() {
        // 1 encoded with 0xFD prefix: 0xFD 0x01 0x00 — non-canonical
        assert_eq!(decode_varint(&[0xFD, 0x01, 0x00]), None);
    }

    #[test]
    fn decode_varint_rejects_non_canonical_fe_for_small_value() {
        // 100 encoded with 0xFE prefix: 0xFE 0x64 0x00 0x00 0x00 — non-canonical
        assert_eq!(
            decode_varint(&[0xFE, 0x64, 0x00, 0x00, 0x00]),
            None
        );
    }

    #[test]
    fn decode_varint_rejects_non_canonical_fe_for_fd_range() {
        // 1000 encoded with 0xFE prefix: non-canonical (fits in 0xFD range)
        assert_eq!(
            decode_varint(&[0xFE, 0xE8, 0x03, 0x00, 0x00]),
            None
        );
    }

    #[test]
    fn decode_varint_rejects_non_canonical_ff_for_small_value() {
        // 1000 encoded with 0xFF prefix: non-canonical
        assert_eq!(
            decode_varint(&[0xFF, 0xE8, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
            None
        );
    }

    // -- truncated data --

    #[test]
    fn decode_varint_fd_truncated() {
        // 0xFD prefix but only 1 byte of payload (needs 2)
        assert_eq!(decode_varint(&[0xFD, 0x00]), None);
    }

    #[test]
    fn decode_varint_fe_truncated() {
        // 0xFE prefix but only 3 bytes of payload (needs 4)
        assert_eq!(decode_varint(&[0xFE, 0x00, 0x00, 0x01]), None);
    }

    #[test]
    fn decode_varint_ff_truncated() {
        // 0xFF prefix but only 7 bytes of payload (needs 8)
        assert_eq!(
            decode_varint(&[0xFF, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00]),
            None
        );
    }

    // -- round-trip --

    #[test]
    fn varint_round_trip_single_byte() {
        for v in 0..=252u64 {
            let encoded = encode_varint(v);
            assert_eq!(encoded.len(), 1);
            let (decoded, consumed) = decode_varint(&encoded).unwrap();
            assert_eq!(decoded, v);
            assert_eq!(consumed, 1);
        }
    }

    #[test]
    fn varint_round_trip_fd_range() {
        for v in [253u64, 254, 255, 256, 1000, 10_000, 65_535] {
            let encoded = encode_varint(v);
            assert_eq!(encoded.len(), 3);
            let (decoded, consumed) = decode_varint(&encoded).unwrap();
            assert_eq!(decoded, v);
            assert_eq!(consumed, 3);
        }
    }

    #[test]
    fn varint_round_trip_fe_range() {
        for v in [65_536u64, 100_000, 1_000_000, 0xFFFF_FFFF] {
            let encoded = encode_varint(v);
            assert_eq!(encoded.len(), 5);
            let (decoded, consumed) = decode_varint(&encoded).unwrap();
            assert_eq!(decoded, v);
            assert_eq!(consumed, 5);
        }
    }

    #[test]
    fn varint_round_trip_ff_range() {
        for v in [0x1_0000_0000u64, 0x1_0000_0001, u64::MAX] {
            let encoded = encode_varint(v);
            assert_eq!(encoded.len(), 9);
            let (decoded, consumed) = decode_varint(&encoded).unwrap();
            assert_eq!(decoded, v);
            assert_eq!(consumed, 9);
        }
    }

    // -- decode with trailing data --

    #[test]
    fn decode_varint_ignores_trailing_data() {
        // 42 followed by extra bytes — decode should consume only 1 byte
        let data = [42u8, 0xDE, 0xAD];
        let (value, consumed) = decode_varint(&data).unwrap();
        assert_eq!(value, 42);
        assert_eq!(consumed, 1);
    }

    #[test]
    fn decode_varint_fd_with_trailing_data() {
        // 0xFD 0x00 0x01 (= 256) followed by extra bytes
        let data = [0xFD, 0x00, 0x01, 0xBE, 0xEF];
        let (value, consumed) = decode_varint(&data).unwrap();
        assert_eq!(value, 256);
        assert_eq!(consumed, 3);
    }

    // -- ML-DSA-44 pk_len varint encoding --

    #[test]
    fn encode_varint_ml_dsa_44_pk_len() {
        // ML-DSA-44 pk is 1312 bytes → varint 0xFD followed by 1312 LE
        // 1312 = 0x0520 → LE bytes: 0x20 0x05
        let encoded = encode_varint(1312);
        assert_eq!(encoded, vec![0xFD, 0x20, 0x05]);
    }

    #[test]
    fn decode_varint_ml_dsa_44_pk_len() {
        let (value, consumed) = decode_varint(&[0xFD, 0x20, 0x05]).unwrap();
        assert_eq!(value, 1312);
        assert_eq!(consumed, 3);
    }
}

// ---------------------------------------------------------------------------
// Single-signature witness Serialize / Parse
// ---------------------------------------------------------------------------

/// Serialize a single-signature witness: `<pk_len: varint> <pk> <sig>`.
///
/// The encoding matches the Coq-verified parse function in
/// `formal/coq/SpendPredPQ.v`: a length prefix followed by the public key
/// bytes followed by the signature bytes (the remaining bytes).
///
/// # Panics
///
/// Does not panic. Empty `pk` or `sig` slices produce a witness that will
/// fail to parse (the parse function rejects empty components).
pub fn serialize_witness(pk: &[u8], sig: &[u8]) -> Vec<u8> {
    let pk_len_varint = encode_varint(pk.len() as u64);
    let mut out = Vec::with_capacity(pk_len_varint.len() + pk.len() + sig.len());
    out.extend_from_slice(&pk_len_varint);
    out.extend_from_slice(pk);
    out.extend_from_slice(sig);
    out
}

/// Parse a single-signature witness into `(pk, sig)`.
///
/// The parse function matches the Coq-verified definition in
/// `formal/coq/SpendPredPQ.v`:
///
/// 1. If `w` is empty → `None`
/// 2. Decode varint `pk_len` from the start of `w`
/// 3. Let `rest = w[varint_size..]`
/// 4. If `pk_len > len(rest)` → `None`
/// 5. `pk = rest[0..pk_len]`, `sig = rest[pk_len..]`
/// 6. If `pk` is empty OR `sig` is empty → `None`
/// 7. Return `Some((pk, sig))`
///
/// Returns `None` for any malformed, truncated, or empty-component witness.
pub fn parse_witness(w: &[u8]) -> Option<(Vec<u8>, Vec<u8>)> {
    if w.is_empty() {
        return None;
    }

    // Step 1: decode the varint pk_len
    let (pk_len, varint_size) = decode_varint(w)?;

    // pk_len must fit in usize for indexing
    let pk_len = usize::try_from(pk_len).ok()?;

    // Step 2: rest is everything after the varint
    let rest = w.get(varint_size..)?;

    // Step 3: pk_len must not exceed remaining bytes
    if pk_len > rest.len() {
        return None;
    }

    // Step 4: split into pk and sig
    let pk = &rest[..pk_len];
    let sig = &rest[pk_len..];

    // Step 5: reject empty components
    if pk.is_empty() || sig.is_empty() {
        return None;
    }

    Some((pk.to_vec(), sig.to_vec()))
}

/// Check whether a witness is in canonical form.
///
/// A witness is canonical iff re-serializing its parsed components produces
/// the exact same byte sequence. This enforces encoding uniqueness and
/// prevents transaction malleability (Requirement 11.4).
///
/// Returns `false` for any witness that fails to parse.
pub fn is_canonical_witness(w: &[u8]) -> bool {
    match parse_witness(w) {
        None => false,
        Some((pk, sig)) => serialize_witness(&pk, &sig) == w,
    }
}

// ---------------------------------------------------------------------------
// Single-signature witness tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod witness_tests {
    use super::*;

    // -- serialize_witness --

    #[test]
    fn serialize_witness_basic() {
        let pk = vec![0x01, 0x02, 0x03];
        let sig = vec![0xAA, 0xBB];
        let w = serialize_witness(&pk, &sig);
        // pk_len = 3 → varint single byte 0x03
        // total: [0x03, 0x01, 0x02, 0x03, 0xAA, 0xBB]
        assert_eq!(w, vec![0x03, 0x01, 0x02, 0x03, 0xAA, 0xBB]);
    }

    #[test]
    fn serialize_witness_ml_dsa_44_size() {
        // ML-DSA-44: pk = 1312 bytes, sig = 2420 bytes
        let pk = vec![0x42; 1312];
        let sig = vec![0x99; 2420];
        let w = serialize_witness(&pk, &sig);
        // varint(1312) = 3 bytes (0xFD prefix) → total = 3 + 1312 + 2420 = 3735
        assert_eq!(w.len(), 3735);
        // First 3 bytes are the varint for 1312
        assert_eq!(&w[..3], &[0xFD, 0x20, 0x05]);
    }

    #[test]
    fn serialize_witness_slh_dsa_128s_size() {
        // SLH-DSA-128s: pk = 32 bytes, sig = 7856 bytes
        let pk = vec![0x42; 32];
        let sig = vec![0x99; 7856];
        let w = serialize_witness(&pk, &sig);
        // varint(32) = 1 byte → total = 1 + 32 + 7856 = 7889
        assert_eq!(w.len(), 7889);
        assert_eq!(w[0], 0x20); // varint for 32
    }

    // -- parse_witness --

    #[test]
    fn parse_witness_empty() {
        assert_eq!(parse_witness(&[]), None);
    }

    #[test]
    fn parse_witness_zero_pk_len() {
        // varint 0 → pk_len = 0 → pk is empty → rejected
        assert_eq!(parse_witness(&[0x00, 0xAA]), None);
    }

    #[test]
    fn parse_witness_pk_len_exceeds_rest() {
        // varint 10 but only 3 bytes of rest
        assert_eq!(parse_witness(&[0x0A, 0x01, 0x02, 0x03]), None);
    }

    #[test]
    fn parse_witness_empty_sig() {
        // varint 3, then exactly 3 bytes of pk, no sig bytes
        assert_eq!(parse_witness(&[0x03, 0x01, 0x02, 0x03]), None);
    }

    #[test]
    fn parse_witness_basic() {
        let w = vec![0x03, 0x01, 0x02, 0x03, 0xAA, 0xBB];
        let (pk, sig) = parse_witness(&w).unwrap();
        assert_eq!(pk, vec![0x01, 0x02, 0x03]);
        assert_eq!(sig, vec![0xAA, 0xBB]);
    }

    #[test]
    fn parse_witness_single_byte_pk_and_sig() {
        // Minimal valid witness: pk_len=1, 1 byte pk, 1 byte sig
        let w = vec![0x01, 0xFF, 0xEE];
        let (pk, sig) = parse_witness(&w).unwrap();
        assert_eq!(pk, vec![0xFF]);
        assert_eq!(sig, vec![0xEE]);
    }

    #[test]
    fn parse_witness_varint_only_no_data() {
        // Just a varint byte with pk_len=1 but no data after it
        assert_eq!(parse_witness(&[0x01]), None);
    }

    #[test]
    fn parse_witness_non_canonical_varint_rejected() {
        // Non-canonical varint: 0xFD 0x01 0x00 encodes value 1 (should be single byte)
        // decode_varint rejects this, so parse_witness returns None
        assert_eq!(parse_witness(&[0xFD, 0x01, 0x00, 0xAA, 0xBB]), None);
    }

    // -- round-trip --

    #[test]
    fn witness_round_trip_basic() {
        let pk = vec![0x01, 0x02, 0x03];
        let sig = vec![0xAA, 0xBB, 0xCC, 0xDD];
        let w = serialize_witness(&pk, &sig);
        let (parsed_pk, parsed_sig) = parse_witness(&w).unwrap();
        assert_eq!(parsed_pk, pk);
        assert_eq!(parsed_sig, sig);
    }

    #[test]
    fn witness_round_trip_ml_dsa_44() {
        let pk = vec![0x42; 1312];
        let sig = vec![0x99; 2420];
        let w = serialize_witness(&pk, &sig);
        let (parsed_pk, parsed_sig) = parse_witness(&w).unwrap();
        assert_eq!(parsed_pk, pk);
        assert_eq!(parsed_sig, sig);
    }

    #[test]
    fn witness_round_trip_slh_dsa_128s() {
        let pk = vec![0x42; 32];
        let sig = vec![0x99; 7856];
        let w = serialize_witness(&pk, &sig);
        let (parsed_pk, parsed_sig) = parse_witness(&w).unwrap();
        assert_eq!(parsed_pk, pk);
        assert_eq!(parsed_sig, sig);
    }

    // -- is_canonical_witness --

    #[test]
    fn canonical_witness_from_serialize() {
        let pk = vec![0x01, 0x02, 0x03];
        let sig = vec![0xAA, 0xBB];
        let w = serialize_witness(&pk, &sig);
        assert!(is_canonical_witness(&w));
    }

    #[test]
    fn canonical_witness_ml_dsa_44() {
        let pk = vec![0x42; 1312];
        let sig = vec![0x99; 2420];
        let w = serialize_witness(&pk, &sig);
        assert!(is_canonical_witness(&w));
    }

    #[test]
    fn non_canonical_witness_trailing_bytes() {
        // A valid witness with extra trailing bytes appended.
        // parse_witness will consume pk_len bytes for pk and treat
        // everything else as sig, so trailing bytes become part of sig.
        // But if we construct a witness and then append bytes, the
        // re-serialized form won't match because sig will be longer.
        let pk = vec![0x01, 0x02, 0x03];
        let sig = vec![0xAA, 0xBB];
        let mut w = serialize_witness(&pk, &sig);
        w.push(0xFF); // trailing byte
        // parse_witness will parse pk=[01,02,03], sig=[AA,BB,FF]
        // re-serialize produces [03, 01,02,03, AA,BB,FF] which != w
        // Actually w = [03, 01,02,03, AA,BB, FF] and re-serialized = [03, 01,02,03, AA,BB,FF]
        // These are the same! The trailing byte just becomes part of sig.
        // So this IS canonical. Let's verify:
        let parsed = parse_witness(&w);
        assert!(parsed.is_some());
        let (ppk, psig) = parsed.unwrap();
        assert_eq!(ppk, pk);
        assert_eq!(psig, vec![0xAA, 0xBB, 0xFF]);
        // Re-serialized matches w, so it IS canonical
        assert!(is_canonical_witness(&w));
    }

    #[test]
    fn non_canonical_witness_non_minimal_varint() {
        // Manually construct a witness with non-minimal varint encoding.
        // pk_len = 3 encoded as 0xFD 0x03 0x00 (non-canonical, should be single byte 0x03)
        // This should fail at decode_varint (canonical check), so parse returns None.
        let w = vec![0xFD, 0x03, 0x00, 0x01, 0x02, 0x03, 0xAA, 0xBB];
        assert!(!is_canonical_witness(&w));
        assert_eq!(parse_witness(&w), None);
    }

    #[test]
    fn non_canonical_empty_witness() {
        assert!(!is_canonical_witness(&[]));
    }

    #[test]
    fn non_canonical_unparseable_witness() {
        // pk_len = 5 but only 2 bytes follow
        assert!(!is_canonical_witness(&[0x05, 0x01, 0x02]));
    }
}

// ---------------------------------------------------------------------------
// Multisig witness Serialize / Parse
// ---------------------------------------------------------------------------

/// Serialize a k-of-n multisig witness.
///
/// Encoding layout (matching the design document):
/// ```text
/// <k: varint> <n: varint>
/// <pk_1_len: varint> <pk_1> ... <pk_n_len: varint> <pk_n>
/// <sig_1_len: varint> <sig_1> ... <sig_k_len: varint> <sig_k>
/// <signer_indices: k raw bytes>
/// ```
///
/// `n` is derived from `pks.len()`. The caller is responsible for ensuring
/// that `k`, `pks`, `sigs`, and `indices` are consistent (e.g., `sigs.len() == k`,
/// `indices.len() == k`). The serialize function does not validate inputs —
/// invalid combinations will produce witnesses that fail to parse.
///
/// # Requirements: 6.5, 11.5
pub fn serialize_multisig_witness(
    k: u8,
    pks: &[Vec<u8>],
    sigs: &[Vec<u8>],
    indices: &[u8],
) -> Vec<u8> {
    let n = pks.len() as u64;
    let mut out = Vec::new();

    // k and n as varints
    out.extend_from_slice(&encode_varint(k as u64));
    out.extend_from_slice(&encode_varint(n));

    // Each public key: length-prefixed
    for pk in pks {
        out.extend_from_slice(&encode_varint(pk.len() as u64));
        out.extend_from_slice(pk);
    }

    // Each signature: length-prefixed
    for sig in sigs {
        out.extend_from_slice(&encode_varint(sig.len() as u64));
        out.extend_from_slice(sig);
    }

    // Signer indices: k raw bytes
    out.extend_from_slice(indices);

    out
}

/// Parse a k-of-n multisig witness into `(k, pks, sigs, indices)`.
///
/// The parse function matches the design document's `Parse_multisig`
/// pseudocode:
///
/// 1. Decode varint `k`, decode varint `n`
/// 2. Reject if `k == 0`, `n == 0`, or `k > n`
/// 3. For each of `n` public keys: decode varint `pk_len`, read `pk_len` bytes
/// 4. For each of `k` signatures: decode varint `sig_len`, read `sig_len` bytes
/// 5. Read exactly `k` bytes as signer indices
/// 6. Reject if any remaining bytes exist
/// 7. Reject if indices are not strictly ascending
/// 8. Reject if any index `>= n`
///
/// Returns `None` for any malformed, truncated, or non-canonical witness.
///
/// # Requirements: 6.5, 6.6, 11.5
pub fn parse_multisig_witness(w: &[u8]) -> Option<(u8, Vec<Vec<u8>>, Vec<Vec<u8>>, Vec<u8>)> {
    if w.is_empty() {
        return None;
    }

    let mut cursor = 0;

    // Decode k
    let (k_val, k_size) = decode_varint(w.get(cursor..)?)?;
    cursor += k_size;
    // k must fit in u8
    if k_val > 255 {
        return None;
    }
    let k = k_val as u8;

    // Decode n
    let (n_val, n_size) = decode_varint(w.get(cursor..)?)?;
    cursor += n_size;
    // n must fit in u8
    if n_val > 255 {
        return None;
    }
    let n = n_val as u8;

    // Reject invalid k/n combinations
    if k == 0 || n == 0 || k > n {
        return None;
    }

    // Read n public keys
    let mut pks = Vec::with_capacity(n as usize);
    for _ in 0..n {
        let remaining = w.get(cursor..)?;
        let (pk_len_val, pk_len_size) = decode_varint(remaining)?;
        cursor += pk_len_size;

        let pk_len = usize::try_from(pk_len_val).ok()?;
        if pk_len == 0 {
            return None;
        }

        let remaining = w.get(cursor..)?;
        if pk_len > remaining.len() {
            return None;
        }
        pks.push(remaining[..pk_len].to_vec());
        cursor += pk_len;
    }

    // Read k signatures
    let mut sigs = Vec::with_capacity(k as usize);
    for _ in 0..k {
        let remaining = w.get(cursor..)?;
        let (sig_len_val, sig_len_size) = decode_varint(remaining)?;
        cursor += sig_len_size;

        let sig_len = usize::try_from(sig_len_val).ok()?;
        if sig_len == 0 {
            return None;
        }

        let remaining = w.get(cursor..)?;
        if sig_len > remaining.len() {
            return None;
        }
        sigs.push(remaining[..sig_len].to_vec());
        cursor += sig_len;
    }

    // Read exactly k bytes for signer indices
    let remaining = w.len() - cursor;
    if remaining != k as usize {
        return None;
    }
    let indices = w[cursor..cursor + k as usize].to_vec();

    // Canonicality: strictly ascending indices
    for i in 0..(k as usize).saturating_sub(1) {
        if indices[i] >= indices[i + 1] {
            return None;
        }
    }

    // All indices must be in range [0, n)
    for &idx in &indices {
        if idx >= n {
            return None;
        }
    }

    Some((k, pks, sigs, indices))
}

// ---------------------------------------------------------------------------
// Multisig witness tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod multisig_witness_tests {
    use super::*;

    // -- serialize_multisig_witness --

    #[test]
    fn serialize_multisig_basic_2_of_3() {
        let pks = vec![vec![0x01; 4], vec![0x02; 4], vec![0x03; 4]];
        let sigs = vec![vec![0xAA; 6], vec![0xBB; 6]];
        let indices = vec![0, 2];
        let w = serialize_multisig_witness(2, &pks, &sigs, &indices);

        // k=2 (1 byte), n=3 (1 byte)
        // 3 pks: each pk_len=4 (1 byte) + 4 bytes = 5 bytes each → 15 bytes
        // 2 sigs: each sig_len=6 (1 byte) + 6 bytes = 7 bytes each → 14 bytes
        // indices: 2 bytes
        // total: 1 + 1 + 15 + 14 + 2 = 33
        assert_eq!(w.len(), 33);
        assert_eq!(w[0], 2); // k
        assert_eq!(w[1], 3); // n
    }

    #[test]
    fn serialize_multisig_1_of_1() {
        let pks = vec![vec![0xFF; 2]];
        let sigs = vec![vec![0xEE; 3]];
        let indices = vec![0];
        let w = serialize_multisig_witness(1, &pks, &sigs, &indices);

        // k=1 (1), n=1 (1), pk_len=2 (1) + pk (2), sig_len=3 (1) + sig (3), index (1)
        // total: 1 + 1 + 1 + 2 + 1 + 3 + 1 = 10
        assert_eq!(w.len(), 10);
    }

    // -- parse_multisig_witness --

    #[test]
    fn parse_multisig_empty() {
        assert_eq!(parse_multisig_witness(&[]), None);
    }

    #[test]
    fn parse_multisig_k_zero() {
        // k=0, n=1 → rejected
        let w = vec![0x00, 0x01];
        assert_eq!(parse_multisig_witness(&w), None);
    }

    #[test]
    fn parse_multisig_n_zero() {
        // k=1, n=0 → rejected
        let w = vec![0x01, 0x00];
        assert_eq!(parse_multisig_witness(&w), None);
    }

    #[test]
    fn parse_multisig_k_greater_than_n() {
        // k=3, n=2 → rejected
        let w = vec![0x03, 0x02];
        assert_eq!(parse_multisig_witness(&w), None);
    }

    #[test]
    fn parse_multisig_empty_pk_rejected() {
        // k=1, n=1, pk_len=0 → rejected
        let w = vec![0x01, 0x01, 0x00];
        assert_eq!(parse_multisig_witness(&w), None);
    }

    #[test]
    fn parse_multisig_empty_sig_rejected() {
        // k=1, n=1, pk_len=1, pk=0xFF, sig_len=0 → rejected
        let w = vec![0x01, 0x01, 0x01, 0xFF, 0x00];
        assert_eq!(parse_multisig_witness(&w), None);
    }

    #[test]
    fn parse_multisig_trailing_bytes_rejected() {
        // Valid 1-of-1 witness with extra trailing byte
        let pks = vec![vec![0x01; 2]];
        let sigs = vec![vec![0xAA; 3]];
        let indices = vec![0];
        let mut w = serialize_multisig_witness(1, &pks, &sigs, &indices);
        w.push(0xFF); // trailing byte
        assert_eq!(parse_multisig_witness(&w), None);
    }

    #[test]
    fn parse_multisig_non_ascending_indices_rejected() {
        // 2-of-3 with indices [1, 0] (not ascending)
        let pks = vec![vec![0x01; 2], vec![0x02; 2], vec![0x03; 2]];
        let sigs = vec![vec![0xAA; 3], vec![0xBB; 3]];
        let indices = vec![1, 0]; // not ascending
        let w = serialize_multisig_witness(2, &pks, &sigs, &indices);
        assert_eq!(parse_multisig_witness(&w), None);
    }

    #[test]
    fn parse_multisig_duplicate_indices_rejected() {
        // 2-of-3 with indices [1, 1] (duplicate, not strictly ascending)
        let pks = vec![vec![0x01; 2], vec![0x02; 2], vec![0x03; 2]];
        let sigs = vec![vec![0xAA; 3], vec![0xBB; 3]];
        let indices = vec![1, 1]; // duplicate
        let w = serialize_multisig_witness(2, &pks, &sigs, &indices);
        assert_eq!(parse_multisig_witness(&w), None);
    }

    #[test]
    fn parse_multisig_index_out_of_range_rejected() {
        // 1-of-2 with index [2] (out of range, n=2 so valid indices are 0,1)
        let pks = vec![vec![0x01; 2], vec![0x02; 2]];
        let sigs = vec![vec![0xAA; 3]];
        let indices = vec![2]; // out of range
        let w = serialize_multisig_witness(1, &pks, &sigs, &indices);
        assert_eq!(parse_multisig_witness(&w), None);
    }

    #[test]
    fn parse_multisig_pk_len_exceeds_remaining() {
        // k=1, n=1, pk_len=100 but only 2 bytes follow
        let w = vec![0x01, 0x01, 0x64, 0xAA, 0xBB];
        assert_eq!(parse_multisig_witness(&w), None);
    }

    #[test]
    fn parse_multisig_sig_len_exceeds_remaining() {
        // k=1, n=1, pk_len=1, pk=0xFF, sig_len=100 but only 2 bytes follow
        let w = vec![0x01, 0x01, 0x01, 0xFF, 0x64, 0xAA, 0xBB];
        assert_eq!(parse_multisig_witness(&w), None);
    }

    // -- round-trip --

    #[test]
    fn multisig_round_trip_1_of_1() {
        let pks = vec![vec![0x42; 10]];
        let sigs = vec![vec![0x99; 20]];
        let indices = vec![0];
        let w = serialize_multisig_witness(1, &pks, &sigs, &indices);
        let (pk, ppks, psigs, pidx) = parse_multisig_witness(&w).unwrap();
        assert_eq!(pk, 1);
        assert_eq!(ppks, pks);
        assert_eq!(psigs, sigs);
        assert_eq!(pidx, indices);
    }

    #[test]
    fn multisig_round_trip_2_of_3() {
        let pks = vec![vec![0x01; 4], vec![0x02; 8], vec![0x03; 6]];
        let sigs = vec![vec![0xAA; 12], vec![0xBB; 16]];
        let indices = vec![0, 2];
        let w = serialize_multisig_witness(2, &pks, &sigs, &indices);
        let (pk, ppks, psigs, pidx) = parse_multisig_witness(&w).unwrap();
        assert_eq!(pk, 2);
        assert_eq!(ppks, pks);
        assert_eq!(psigs, sigs);
        assert_eq!(pidx, indices);
    }

    #[test]
    fn multisig_round_trip_3_of_3() {
        let pks = vec![vec![0x01; 32], vec![0x02; 32], vec![0x03; 32]];
        let sigs = vec![vec![0xAA; 64], vec![0xBB; 64], vec![0xCC; 64]];
        let indices = vec![0, 1, 2];
        let w = serialize_multisig_witness(3, &pks, &sigs, &indices);
        let (pk, ppks, psigs, pidx) = parse_multisig_witness(&w).unwrap();
        assert_eq!(pk, 3);
        assert_eq!(ppks, pks);
        assert_eq!(psigs, sigs);
        assert_eq!(pidx, indices);
    }

    #[test]
    fn multisig_round_trip_ml_dsa_44_2_of_3() {
        // Realistic ML-DSA-44 sizes
        let pks = vec![vec![0x42; 1312], vec![0x43; 1312], vec![0x44; 1312]];
        let sigs = vec![vec![0x99; 2420], vec![0x9A; 2420]];
        let indices = vec![0, 2];
        let w = serialize_multisig_witness(2, &pks, &sigs, &indices);
        let (pk, ppks, psigs, pidx) = parse_multisig_witness(&w).unwrap();
        assert_eq!(pk, 2);
        assert_eq!(ppks, pks);
        assert_eq!(psigs, sigs);
        assert_eq!(pidx, indices);
    }

    #[test]
    fn multisig_round_trip_1_of_n_max_index() {
        // 1-of-5 selecting the last key
        let pks: Vec<Vec<u8>> = (0..5).map(|i| vec![i; 10]).collect();
        let sigs = vec![vec![0xAA; 20]];
        let indices = vec![4]; // last valid index
        let w = serialize_multisig_witness(1, &pks, &sigs, &indices);
        let (pk, ppks, psigs, pidx) = parse_multisig_witness(&w).unwrap();
        assert_eq!(pk, 1);
        assert_eq!(ppks, pks);
        assert_eq!(psigs, sigs);
        assert_eq!(pidx, indices);
    }

    // -- edge cases for k and n fitting in u8 --

    #[test]
    fn parse_multisig_k_exceeds_u8_rejected() {
        // Manually construct a witness with k=256 (varint 0xFD 0x00 0x01)
        // This should be rejected because k doesn't fit in u8
        let mut w = Vec::new();
        w.extend_from_slice(&encode_varint(256)); // k = 256
        w.extend_from_slice(&encode_varint(256)); // n = 256
        // Don't need to add more — should fail at k > 255 check
        assert_eq!(parse_multisig_witness(&w), None);
    }
}
