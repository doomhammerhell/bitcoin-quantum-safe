//! Consensus parameters and constants for the PQ witness protocol.
//!
//! Defines witness version, size limits, block weight budget, cost constants,
//! PQ scheme key/signature sizes, and migration configuration.
//!
//! All values are derived from the design document's Consensus Parameters table
//! and the formal results of "Toward Protocol-Level Quantum Safety in Bitcoin"
//! (Giovani, 2026).

// ---------------------------------------------------------------------------
// Witness version
// ---------------------------------------------------------------------------

/// SegWit witness version for post-quantum outputs.
///
/// Version 2 is the next available after Taproot v1 (Req 7.6).
/// Non-upgraded nodes treat v2 outputs as anyone-can-spend (BIP 141).
pub const WITNESS_VERSION: u8 = 2;

// ---------------------------------------------------------------------------
// Witness size limits
// ---------------------------------------------------------------------------

/// Maximum witness byte length enforced before cryptographic verification.
///
/// Caps the effective `n` for multisig (~4× SLH-DSA-128s single-sig).
/// Witnesses exceeding this limit are rejected without parsing (Req 2.9, 8.3).
pub const MAX_WITNESS_SIZE: usize = 16_000;

// ---------------------------------------------------------------------------
// Block weight budget
// ---------------------------------------------------------------------------

/// Block cost cap in weight units (WU).
///
/// Equal to the existing 4 MWU block weight limit — no hard fork required
/// (Req 3.5, 8.1). Derived from the target ≤ 2 s block validation time on
/// commodity hardware at ~10,000 ML-DSA-44 verifications/s.
pub const C_MAX: u64 = 4_000_000;

/// Cost constant α: `Cost(tx) ≤ α · weight(tx)`.
///
/// α = 1 because PQ witness bytes are already accounted at 1 WU/byte under
/// the SegWit witness discount (Req 3.1).
pub const ALPHA: u64 = 1;

// ---------------------------------------------------------------------------
// ML-DSA-44 (FIPS 204) sizes
// ---------------------------------------------------------------------------

/// ML-DSA-44 public key length in bytes.
///
/// NIST FIPS 204, security level 2 (128-bit quantum security) (Req 1.1).
pub const ML_DSA_44_PK_LEN: usize = 1_312;

/// ML-DSA-44 signature length in bytes.
pub const ML_DSA_44_SIG_LEN: usize = 2_420;

// ---------------------------------------------------------------------------
// SLH-DSA-128s (FIPS 205) sizes
// ---------------------------------------------------------------------------

/// SLH-DSA-128s public key length in bytes.
///
/// Conservative hash-based scheme, 128-bit quantum security (Req 1.2).
pub const SLH_DSA_128S_PK_LEN: usize = 32;

/// SLH-DSA-128s signature length in bytes.
pub const SLH_DSA_128S_SIG_LEN: usize = 7_856;

// ---------------------------------------------------------------------------
// Commitment
// ---------------------------------------------------------------------------

/// SHA-256 commitment length in bytes: P = H(pk).
///
/// 2^128 quantum preimage resistance under Grover (Req 1.4).
pub const COMMITMENT_LEN: usize = 32;

// ---------------------------------------------------------------------------
// Migration timing
// ---------------------------------------------------------------------------

/// Minimum grace period in blocks: `H_c - H_a ≥ 26_280` (~6 months).
///
/// The absolute minimum viable migration window (Req 4.6).
pub const MIN_GRACE_PERIOD: u64 = 26_280;

/// Recommended grace period in blocks (~1 year at ~10 min/block).
///
/// Two full key rotation cycles for institutional custody (Req 4.6, 12.3).
pub const RECOMMENDED_GRACE_PERIOD: u64 = 52_560;

// ---------------------------------------------------------------------------
// MigrationConfig
// ---------------------------------------------------------------------------

/// Configuration for the three-phase migration timeline.
///
/// * `announcement_height` (H_a) — block height at which the PQ witness
///   version activates and new legacy output creation is prohibited.
/// * `cutover_height` (H_c) — block height after which legacy spend
///   predicates are rejected and unmigrated outputs are frozen.
///
/// The grace period `[H_a, H_c)` must be at least [`MIN_GRACE_PERIOD`]
/// blocks to give holders adequate migration time (Req 4.6).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MigrationConfig {
    /// Announcement height H_a.
    pub announcement_height: u64,
    /// Cutover height H_c.
    pub cutover_height: u64,
}

impl MigrationConfig {
    /// Create a new `MigrationConfig`, validating the grace period constraint.
    ///
    /// Returns `Err` if `cutover_height - announcement_height < MIN_GRACE_PERIOD`
    /// (26,280 blocks, ~6 months) or if `cutover_height <= announcement_height`.
    ///
    /// # Examples
    ///
    /// ```
    /// use pq_witness_protocol::params::MigrationConfig;
    ///
    /// // Valid: exactly the minimum grace period
    /// let cfg = MigrationConfig::new(100_000, 126_280).unwrap();
    /// assert_eq!(cfg.announcement_height, 100_000);
    /// assert_eq!(cfg.cutover_height, 126_280);
    ///
    /// // Invalid: grace period too short
    /// assert!(MigrationConfig::new(100_000, 110_000).is_err());
    /// ```
    pub fn new(announcement_height: u64, cutover_height: u64) -> Result<Self, String> {
        if cutover_height <= announcement_height {
            return Err(format!(
                "cutover_height ({}) must be greater than announcement_height ({})",
                cutover_height, announcement_height
            ));
        }

        let grace = cutover_height - announcement_height;
        if grace < MIN_GRACE_PERIOD {
            return Err(format!(
                "grace period {} blocks is below the minimum {} blocks (~6 months)",
                grace, MIN_GRACE_PERIOD
            ));
        }

        Ok(Self {
            announcement_height,
            cutover_height,
        })
    }

    /// Convenience constructor using the recommended ~1 year grace period.
    ///
    /// Sets `cutover_height = announcement_height + RECOMMENDED_GRACE_PERIOD`.
    pub fn with_recommended_grace(announcement_height: u64) -> Self {
        Self {
            announcement_height,
            cutover_height: announcement_height + RECOMMENDED_GRACE_PERIOD,
        }
    }

    /// Returns the grace period length in blocks.
    pub fn grace_period(&self) -> u64 {
        self.cutover_height - self.announcement_height
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- constant sanity checks --

    #[test]
    fn witness_version_is_two() {
        assert_eq!(WITNESS_VERSION, 2);
    }

    #[test]
    fn max_witness_size_value() {
        assert_eq!(MAX_WITNESS_SIZE, 16_000);
    }

    #[test]
    fn c_max_is_four_million() {
        assert_eq!(C_MAX, 4_000_000);
    }

    #[test]
    fn alpha_is_one() {
        assert_eq!(ALPHA, 1);
    }

    #[test]
    fn ml_dsa_44_sizes() {
        assert_eq!(ML_DSA_44_PK_LEN, 1_312);
        assert_eq!(ML_DSA_44_SIG_LEN, 2_420);
    }

    #[test]
    fn slh_dsa_128s_sizes() {
        assert_eq!(SLH_DSA_128S_PK_LEN, 32);
        assert_eq!(SLH_DSA_128S_SIG_LEN, 7_856);
    }

    #[test]
    fn commitment_len_is_32() {
        assert_eq!(COMMITMENT_LEN, 32);
    }

    #[test]
    fn recommended_grace_period_value() {
        assert_eq!(RECOMMENDED_GRACE_PERIOD, 52_560);
    }

    #[test]
    fn min_grace_period_value() {
        assert_eq!(MIN_GRACE_PERIOD, 26_280);
    }

    // -- MigrationConfig --

    #[test]
    fn migration_config_valid_minimum_grace() {
        let cfg = MigrationConfig::new(100_000, 100_000 + MIN_GRACE_PERIOD).unwrap();
        assert_eq!(cfg.announcement_height, 100_000);
        assert_eq!(cfg.cutover_height, 100_000 + MIN_GRACE_PERIOD);
        assert_eq!(cfg.grace_period(), MIN_GRACE_PERIOD);
    }

    #[test]
    fn migration_config_valid_recommended_grace() {
        let cfg = MigrationConfig::new(100_000, 100_000 + RECOMMENDED_GRACE_PERIOD).unwrap();
        assert_eq!(cfg.grace_period(), RECOMMENDED_GRACE_PERIOD);
    }

    #[test]
    fn migration_config_valid_large_grace() {
        // Larger than recommended is fine.
        let cfg = MigrationConfig::new(100_000, 300_000).unwrap();
        assert_eq!(cfg.grace_period(), 200_000);
    }

    #[test]
    fn migration_config_rejects_short_grace() {
        let result = MigrationConfig::new(100_000, 110_000);
        assert!(result.is_err());
        let msg = result.unwrap_err();
        assert!(msg.contains("below the minimum"));
    }

    #[test]
    fn migration_config_rejects_equal_heights() {
        let result = MigrationConfig::new(100_000, 100_000);
        assert!(result.is_err());
        let msg = result.unwrap_err();
        assert!(msg.contains("must be greater than"));
    }

    #[test]
    fn migration_config_rejects_cutover_before_announcement() {
        let result = MigrationConfig::new(100_000, 50_000);
        assert!(result.is_err());
    }

    #[test]
    fn migration_config_rejects_one_block_short_of_minimum() {
        // Exactly MIN_GRACE_PERIOD - 1 should fail.
        let result = MigrationConfig::new(100_000, 100_000 + MIN_GRACE_PERIOD - 1);
        assert!(result.is_err());
    }

    #[test]
    fn migration_config_with_recommended_grace() {
        let cfg = MigrationConfig::with_recommended_grace(200_000);
        assert_eq!(cfg.announcement_height, 200_000);
        assert_eq!(cfg.cutover_height, 200_000 + RECOMMENDED_GRACE_PERIOD);
        assert_eq!(cfg.grace_period(), RECOMMENDED_GRACE_PERIOD);
    }

    #[test]
    fn migration_config_with_recommended_grace_at_zero() {
        let cfg = MigrationConfig::with_recommended_grace(0);
        assert_eq!(cfg.announcement_height, 0);
        assert_eq!(cfg.cutover_height, RECOMMENDED_GRACE_PERIOD);
    }

    // -- derived size checks from the design document --

    #[test]
    fn ml_dsa_44_single_sig_witness_fits() {
        // varint(1312) = 3 bytes (0xFD prefix) + 1312 pk + 2420 sig = 3735
        let witness_size = 3 + ML_DSA_44_PK_LEN + ML_DSA_44_SIG_LEN;
        assert!(witness_size <= MAX_WITNESS_SIZE);
    }

    #[test]
    fn slh_dsa_128s_single_sig_witness_fits() {
        // varint(32) = 1 byte + 32 pk + 7856 sig = 7889
        let witness_size = 1 + SLH_DSA_128S_PK_LEN + SLH_DSA_128S_SIG_LEN;
        assert!(witness_size <= MAX_WITNESS_SIZE);
    }
}
