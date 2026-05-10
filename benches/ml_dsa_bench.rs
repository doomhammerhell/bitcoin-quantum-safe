//! ML-DSA-44 Performance Benchmarks
//!
//! Measures throughput of key operations for the PQ witness protocol:
//! - Key generation (less critical for consensus)
//! - Signing (one-time per transaction)
//! - Verification (critical for block validation)
//!
//! These benchmarks validate the paper's assumption of ~10,000 ML-DSA-44
//! verifications per second on commodity hardware.
//!
//! Run with: cargo bench --bench ml_dsa_bench

use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use fips204::ml_dsa_44;
use fips204::traits::{SerDes, Signer, Verifier};

/// Benchmark key generation throughput
fn bench_keygen(c: &mut Criterion) {
    let mut group = c.benchmark_group("ml_dsa_44_keygen");
    group.throughput(Throughput::Elements(1));

    group.bench_function("keygen", |b| {
        b.iter(|| {
            let (_pk, _sk) = ml_dsa_44::try_keygen().unwrap();
            black_box(_pk);
        });
    });

    group.finish();
}

/// Benchmark signing throughput
fn bench_sign(c: &mut Criterion) {
    // Generate a test keypair
    let (pk, sk) = ml_dsa_44::try_keygen().unwrap();
    let _pk_bytes = pk.into_bytes(); // prefixed with _ to suppress unused warning

    // Test message
    let message = b"benchmark test message for ml-dsa-44 signing";

    let mut group = c.benchmark_group("ml_dsa_44_sign");
    group.throughput(Throughput::Bytes(message.len() as u64));

    group.bench_function("sign", |b| {
        b.iter(|| {
            let sig = sk.try_sign(black_box(message), &[]).unwrap();
            black_box(sig);
        });
    });

    group.finish();
}

/// Benchmark verification throughput - MOST CRITICAL for consensus
fn bench_verify(c: &mut Criterion) {
    // Generate a test keypair and signature
    let (pk, sk) = ml_dsa_44::try_keygen().unwrap();
    let pk_bytes = pk.into_bytes();
    let message = b"benchmark test message for ml-dsa-44 verification";
    let sig = sk.try_sign(message, &[]).unwrap();

    // Reconstruct public key from bytes (as consensus would)
    let pk_reconstructed = ml_dsa_44::PublicKey::try_from_bytes(pk_bytes).unwrap();

    let mut group = c.benchmark_group("ml_dsa_44_verify");
    group.throughput(Throughput::Elements(1));

    group.bench_function("verify", |b| {
        b.iter(|| {
            let result =
                pk_reconstructed.verify(black_box(message), black_box(&sig), black_box(&[]));
            assert!(result, "Verification should succeed");
            black_box(result);
        });
    });

    group.finish();
}

/// Benchmark batch verification throughput
fn bench_batch_verify(c: &mut Criterion) {
    // Generate multiple keypairs and signatures
    const BATCH_SIZE: usize = 100;
    let mut pks = Vec::with_capacity(BATCH_SIZE);
    let mut sigs = Vec::with_capacity(BATCH_SIZE);
    let message = b"batch verification benchmark message";

    for _ in 0..BATCH_SIZE {
        let (pk, sk) = ml_dsa_44::try_keygen().unwrap();
        let sig = sk.try_sign(message, &[]).unwrap();
        pks.push(pk);
        sigs.push(sig);
    }

    let mut group = c.benchmark_group("ml_dsa_44_batch");
    group.throughput(Throughput::Elements(BATCH_SIZE as u64));

    group.bench_function("batch_100", |b| {
        b.iter(|| {
            for i in 0..BATCH_SIZE {
                let result = pks[i].verify(black_box(message), black_box(&sigs[i]), black_box(&[]));
                assert!(result, "Verification should succeed");
            }
        });
    });

    group.finish();
}

/// Measure sustained verification throughput over time
fn bench_sustained_verify(c: &mut Criterion) {
    let (pk, sk) = ml_dsa_44::try_keygen().unwrap();
    let message = b"sustained verification benchmark";
    let sig = sk.try_sign(message, &[]).unwrap();

    let mut group = c.benchmark_group("ml_dsa_44_sustained");
    group.measurement_time(std::time::Duration::from_secs(10));
    group.throughput(Throughput::Elements(1));

    group.bench_function("verify_10s", |b| {
        b.iter(|| {
            let result = pk.verify(black_box(message), black_box(&sig), black_box(&[]));
            assert!(result);
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_keygen,
    bench_sign,
    bench_verify,
    bench_batch_verify,
    bench_sustained_verify
);
criterion_main!(benches);
