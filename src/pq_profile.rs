//! Cryptographic suite profile for the PQ consensus witness.
//!
//! This module makes the protocol's cryptographic agility boundary explicit:
//! standard-aligned parameter sets may be modeled and costed before they are
//! consensus-enabled, but consensus validation only accepts schemes with a
//! deployed verifier and a matching refinement boundary.

use crate::encoding::encode_varint;
use crate::params::{
    MAX_WITNESS_SIZE, ML_DSA_44_PK_LEN, ML_DSA_44_SIG_LEN, SLH_DSA_128S_PK_LEN,
    SLH_DSA_128S_SIG_LEN,
};

/// Post-quantum signature standard family.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PqStandard {
    /// NIST FIPS 204: Module-Lattice-Based Digital Signature Standard.
    Fips204,
    /// NIST FIPS 205: Stateless Hash-Based Digital Signature Standard.
    Fips205,
}

/// Cryptographic assumption family used for defense-in-depth reasoning.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PqAssumptionFamily {
    /// Module-lattice signature assumption family.
    ModuleLattice,
    /// Stateless hash-based signature assumption family.
    HashBased,
}

/// Protocol role for a profiled signature scheme.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PqSchemeRole {
    /// Scheme used by the current deployed consensus verifier.
    PrimaryConsensus,
    /// Standards-aligned fallback profile reserved until verifier activation.
    ConservativeFallback,
}

/// Signature schemes currently tracked by the protocol profile.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PqSignatureScheme {
    /// ML-DSA-44, the FIPS 204 scheme implemented by the current spend predicate.
    MlDsa44,
    /// SLH-DSA-128s, a FIPS 205 hash-based fallback profile.
    SlhDsa128s,
}

/// Auditable profile for a PQ signature scheme.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct PqSchemeProfile {
    pub scheme: PqSignatureScheme,
    pub standard: PqStandard,
    pub role: PqSchemeRole,
    pub assumption_family: PqAssumptionFamily,
    pub target_quantum_security_bits: u16,
    pub public_key_len: usize,
    pub signature_len: usize,
    pub implemented_verifier: bool,
}

/// The deployed consensus verifier's signature scheme.
pub fn primary_signature_scheme() -> PqSignatureScheme {
    PqSignatureScheme::MlDsa44
}

/// The conservative standards-aligned fallback profile.
pub fn fallback_signature_scheme() -> PqSignatureScheme {
    PqSignatureScheme::SlhDsa128s
}

/// Return the fixed profile for a tracked PQ signature scheme.
pub fn profile_for_scheme(scheme: PqSignatureScheme) -> PqSchemeProfile {
    match scheme {
        PqSignatureScheme::MlDsa44 => PqSchemeProfile {
            scheme,
            standard: PqStandard::Fips204,
            role: PqSchemeRole::PrimaryConsensus,
            assumption_family: PqAssumptionFamily::ModuleLattice,
            target_quantum_security_bits: 128,
            public_key_len: ML_DSA_44_PK_LEN,
            signature_len: ML_DSA_44_SIG_LEN,
            implemented_verifier: true,
        },
        PqSignatureScheme::SlhDsa128s => PqSchemeProfile {
            scheme,
            standard: PqStandard::Fips205,
            role: PqSchemeRole::ConservativeFallback,
            assumption_family: PqAssumptionFamily::HashBased,
            target_quantum_security_bits: 128,
            public_key_len: SLH_DSA_128S_PK_LEN,
            signature_len: SLH_DSA_128S_SIG_LEN,
            implemented_verifier: false,
        },
    }
}

/// All signature profiles tracked by the protocol.
pub fn all_signature_profiles() -> [PqSchemeProfile; 2] {
    [
        profile_for_scheme(PqSignatureScheme::MlDsa44),
        profile_for_scheme(PqSignatureScheme::SlhDsa128s),
    ]
}

/// Profiles that currently have a deployed consensus verifier.
pub fn implemented_signature_profiles() -> Vec<PqSchemeProfile> {
    all_signature_profiles()
        .into_iter()
        .filter(|profile| profile.implemented_verifier)
        .collect()
}

fn compact_size_len(value: usize) -> Option<usize> {
    let value = u64::try_from(value).ok()?;
    Some(encode_varint(value).len())
}

/// Consensus witness bytes for a single-signature witness under this profile.
pub fn witness_size_for_profile(profile: PqSchemeProfile) -> Option<usize> {
    let pk_len_prefix = compact_size_len(profile.public_key_len)?;
    let sig_len_prefix = compact_size_len(profile.signature_len)?;

    pk_len_prefix
        .checked_add(profile.public_key_len)?
        .checked_add(sig_len_prefix)?
        .checked_add(profile.signature_len)
}

/// Whether the profiled single-signature witness fits the consensus witness cap.
pub fn profile_fits_consensus_witness_cap(profile: PqSchemeProfile) -> bool {
    witness_size_for_profile(profile).is_some_and(|size| size <= MAX_WITNESS_SIZE)
}

/// Identify a profiled scheme from exact public-key and signature lengths.
pub fn scheme_for_witness_lengths(pk_len: usize, sig_len: usize) -> Option<PqSignatureScheme> {
    all_signature_profiles()
        .into_iter()
        .find(|profile| profile.public_key_len == pk_len && profile.signature_len == sig_len)
        .map(|profile| profile.scheme)
}

/// Identify a consensus-enabled scheme from exact public-key and signature lengths.
///
/// This deliberately rejects standards-aligned profiles that lack an implemented
/// verifier. That prevents future agility metadata from widening consensus
/// acceptance before the corresponding verification/refinement artifacts exist.
pub fn consensus_supported_signature_scheme(
    pk_len: usize,
    sig_len: usize,
) -> Option<PqSignatureScheme> {
    let profile = all_signature_profiles()
        .into_iter()
        .find(|profile| profile.public_key_len == pk_len && profile.signature_len == sig_len)?;

    profile.implemented_verifier.then_some(profile.scheme)
}

/// Whether a public-key length belongs to a consensus-enabled profile.
pub fn consensus_supported_public_key_len(pk_len: usize) -> bool {
    all_signature_profiles()
        .into_iter()
        .any(|profile| profile.implemented_verifier && profile.public_key_len == pk_len)
}

/// Whether the current active suite is standards-aligned and diversified.
pub fn active_suite_is_standards_aligned() -> bool {
    let primary = profile_for_scheme(primary_signature_scheme());
    let fallback = profile_for_scheme(fallback_signature_scheme());

    primary.implemented_verifier
        && primary.standard == PqStandard::Fips204
        && fallback.standard == PqStandard::Fips205
        && primary.assumption_family != fallback.assumption_family
        && profile_fits_consensus_witness_cap(primary)
        && profile_fits_consensus_witness_cap(fallback)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primary_profile_matches_ml_dsa_44_parameters() {
        let profile = profile_for_scheme(primary_signature_scheme());
        assert_eq!(profile.scheme, PqSignatureScheme::MlDsa44);
        assert_eq!(profile.standard, PqStandard::Fips204);
        assert_eq!(profile.role, PqSchemeRole::PrimaryConsensus);
        assert_eq!(profile.assumption_family, PqAssumptionFamily::ModuleLattice);
        assert_eq!(profile.target_quantum_security_bits, 128);
        assert_eq!(profile.public_key_len, ML_DSA_44_PK_LEN);
        assert_eq!(profile.signature_len, ML_DSA_44_SIG_LEN);
        assert!(profile.implemented_verifier);
        assert_eq!(witness_size_for_profile(profile), Some(3_738));
    }

    #[test]
    fn fallback_profile_matches_slh_dsa_128s_parameters() {
        let profile = profile_for_scheme(fallback_signature_scheme());
        assert_eq!(profile.scheme, PqSignatureScheme::SlhDsa128s);
        assert_eq!(profile.standard, PqStandard::Fips205);
        assert_eq!(profile.role, PqSchemeRole::ConservativeFallback);
        assert_eq!(profile.assumption_family, PqAssumptionFamily::HashBased);
        assert_eq!(profile.target_quantum_security_bits, 128);
        assert_eq!(profile.public_key_len, SLH_DSA_128S_PK_LEN);
        assert_eq!(profile.signature_len, SLH_DSA_128S_SIG_LEN);
        assert!(!profile.implemented_verifier);
        assert_eq!(witness_size_for_profile(profile), Some(7_892));
    }

    #[test]
    fn profiled_witnesses_fit_current_consensus_cap() {
        for profile in all_signature_profiles() {
            assert!(profile_fits_consensus_witness_cap(profile));
        }
    }

    #[test]
    fn witness_lengths_identify_profiled_schemes() {
        assert_eq!(
            scheme_for_witness_lengths(ML_DSA_44_PK_LEN, ML_DSA_44_SIG_LEN),
            Some(PqSignatureScheme::MlDsa44)
        );
        assert_eq!(
            scheme_for_witness_lengths(SLH_DSA_128S_PK_LEN, SLH_DSA_128S_SIG_LEN),
            Some(PqSignatureScheme::SlhDsa128s)
        );
        assert_eq!(scheme_for_witness_lengths(ML_DSA_44_PK_LEN, 64), None);
    }

    #[test]
    fn consensus_acceptance_requires_implemented_verifier() {
        assert_eq!(
            consensus_supported_signature_scheme(ML_DSA_44_PK_LEN, ML_DSA_44_SIG_LEN),
            Some(PqSignatureScheme::MlDsa44)
        );
        assert_eq!(
            consensus_supported_signature_scheme(SLH_DSA_128S_PK_LEN, SLH_DSA_128S_SIG_LEN),
            None
        );
        assert!(consensus_supported_public_key_len(ML_DSA_44_PK_LEN));
        assert!(!consensus_supported_public_key_len(SLH_DSA_128S_PK_LEN));
    }

    #[test]
    fn implemented_profiles_only_include_consensus_active_schemes() {
        assert_eq!(
            implemented_signature_profiles(),
            vec![profile_for_scheme(PqSignatureScheme::MlDsa44)]
        );
    }

    #[test]
    fn active_suite_has_distinct_assumption_families() {
        let primary = profile_for_scheme(primary_signature_scheme());
        let fallback = profile_for_scheme(fallback_signature_scheme());
        assert_ne!(primary.assumption_family, fallback.assumption_family);
        assert!(active_suite_is_standards_aligned());
    }
}
