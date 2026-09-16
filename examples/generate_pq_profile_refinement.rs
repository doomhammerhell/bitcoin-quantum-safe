//! Rust-side PQ signature-suite profile refinement summary.
//!
//! This executable mirrors the Coq-extracted PQProfile summary. CI compares the
//! JSON objects exactly, and the release validator records source/binary hashes.

use pq_witness_protocol::{
    active_suite_is_standards_aligned, all_signature_profiles, fallback_signature_scheme,
    implemented_signature_profiles, primary_signature_scheme, profile_fits_consensus_witness_cap,
    profile_for_scheme, witness_size_for_profile, PqAssumptionFamily, PqSchemeProfile,
    PqSchemeRole, PqSignatureScheme, PqStandard,
};
use serde_json::{json, Value};

fn scheme_name(scheme: PqSignatureScheme) -> &'static str {
    match scheme {
        PqSignatureScheme::MlDsa44 => "ML-DSA-44",
        PqSignatureScheme::SlhDsa128s => "SLH-DSA-128s",
    }
}

fn standard_name(standard: PqStandard) -> &'static str {
    match standard {
        PqStandard::Fips204 => "FIPS 204",
        PqStandard::Fips205 => "FIPS 205",
    }
}

fn role_name(role: PqSchemeRole) -> &'static str {
    match role {
        PqSchemeRole::PrimaryConsensus => "primary_consensus",
        PqSchemeRole::ConservativeFallback => "conservative_fallback",
    }
}

fn assumption_family_name(family: PqAssumptionFamily) -> &'static str {
    match family {
        PqAssumptionFamily::ModuleLattice => "module_lattice",
        PqAssumptionFamily::HashBased => "hash_based",
    }
}

fn profile_json(profile: PqSchemeProfile) -> Value {
    json!({
        "scheme": scheme_name(profile.scheme),
        "standard": standard_name(profile.standard),
        "role": role_name(profile.role),
        "assumption_family": assumption_family_name(profile.assumption_family),
        "target_quantum_security_bits": profile.target_quantum_security_bits,
        "public_key_len": profile.public_key_len,
        "signature_len": profile.signature_len,
        "witness_size": witness_size_for_profile(profile).expect("profile sizes fit usize"),
        "fits_consensus_witness_cap": profile_fits_consensus_witness_cap(profile),
        "implemented_verifier": profile.implemented_verifier,
        "consensus_enabled": profile.implemented_verifier
            && profile_fits_consensus_witness_cap(profile),
        "primary": profile.scheme == primary_signature_scheme(),
        "fallback": profile.scheme == fallback_signature_scheme(),
    })
}

fn main() {
    let profiles = all_signature_profiles();
    let implemented_schemes: Vec<_> = implemented_signature_profiles()
        .into_iter()
        .map(|profile| scheme_name(profile.scheme))
        .collect();
    let consensus_enabled_schemes: Vec<_> = profiles
        .into_iter()
        .filter(|profile| {
            profile.implemented_verifier && profile_fits_consensus_witness_cap(*profile)
        })
        .map(|profile| scheme_name(profile.scheme))
        .collect();

    let primary = profile_for_scheme(primary_signature_scheme());
    let fallback = profile_for_scheme(fallback_signature_scheme());

    let summary = json!({
        "model": "pq-signature-profile-refinement",
        "profile_count": all_signature_profiles().len(),
        "max_consensus_witness_size": pq_witness_protocol::MAX_WITNESS_SIZE,
        "profiles": all_signature_profiles()
            .into_iter()
            .map(profile_json)
            .collect::<Vec<_>>(),
        "primary_scheme": scheme_name(primary_signature_scheme()),
        "fallback_scheme": scheme_name(fallback_signature_scheme()),
        "implemented_schemes": implemented_schemes,
        "consensus_enabled_schemes": consensus_enabled_schemes,
        "properties": {
            "standards_distinct": primary.standard != fallback.standard,
            "assumption_families_distinct": primary.assumption_family != fallback.assumption_family,
            "tracked_profiles_fit_current_consensus_cap": all_signature_profiles()
                .into_iter()
                .all(profile_fits_consensus_witness_cap),
            "consensus_enabled_exactly_primary": all_signature_profiles()
                .into_iter()
                .all(|profile| {
                    let consensus_enabled =
                        profile.implemented_verifier && profile_fits_consensus_witness_cap(profile);
                    consensus_enabled == (profile.scheme == primary_signature_scheme())
                }),
            "active_suite_standards_aligned": active_suite_is_standards_aligned(),
        },
    });

    println!("{}", serde_json::to_string_pretty(&summary).unwrap());
}
