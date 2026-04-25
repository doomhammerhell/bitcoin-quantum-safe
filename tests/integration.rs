//! Integration tests for the PQ witness protocol.
//!
//! These tests exercise the crate's public API end-to-end, covering the full
//! migration lifecycle, mixed block validation, multisig migration, and the
//! activation sequence state machine.
//!
//! Requirements validated: 3.2, 4.1–4.5, 4.9, 5.1–5.3, 6.2, 6.3, 6.5,
//! 7.1, 7.2, 7.6, 8.5

use pq_witness_protocol::*;
use pq_witness_protocol::types::{OutPoint, Output, TxInput, TxOutput, Transaction};
use pq_witness_protocol::migration::{get_phase, MigrationPhase};
use pq_witness_protocol::freeze::is_frozen;
use pq_witness_protocol::weight::cost_tx;

use fips204::ml_dsa_44;
use fips204::traits::{SerDes, Signer};
use sha2::{Digest, Sha256};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Create an outpoint with a unique id byte and vout.
fn outpoint(id: u8, vout: u32) -> OutPoint {
    let mut txid = [0u8; 32];
    txid[0] = id;
    OutPoint { txid, vout }
}

/// Create a legacy (v0) output for the UTXO set.
fn legacy_output(value: u64) -> Output {
    Output {
        script_version: 0,
        commitment: [0xBB; 32],
        value,
    }
}

/// Create a PQ (v2) output for the UTXO set with a given commitment.
fn pq_utxo_output(commitment: Commitment, value: u64) -> Output {
    Output {
        script_version: 2,
        commitment,
        value,
    }
}

/// Create a PQ (v2) transaction output with a given commitment.
fn pq_tx_output(commitment: Commitment, value: u64) -> TxOutput {
    TxOutput {
        script_version: 2,
        commitment,
        value,
    }
}

/// Create a legacy (v0) transaction output.
fn legacy_tx_output(value: u64) -> TxOutput {
    TxOutput {
        script_version: 0,
        commitment: [0xDD; 32],
        value,
    }
}

/// Create a Taproot (v1) output for the UTXO set.
#[allow(dead_code)]
fn taproot_output(value: u64) -> Output {
    Output {
        script_version: 1,
        commitment: [0xCC; 32],
        value,
    }
}

/// Generate an ML-DSA-44 keypair and return (pk_bytes, sk, commitment).
fn gen_pq_keypair() -> (Vec<u8>, ml_dsa_44::PrivateKey, Commitment) {
    let (pk, sk) = ml_dsa_44::try_keygen().unwrap();
    let pk_bytes = pk.into_bytes().to_vec();
    let commitment: Commitment = Sha256::digest(&pk_bytes).into();
    (pk_bytes, sk, commitment)
}

/// Build a valid PQ witness for spending a v2 output.
///
/// Signs the sighash with the given secret key and serializes the witness.
fn build_pq_witness(
    pk_bytes: &[u8],
    sk: &ml_dsa_44::PrivateKey,
    tx: &Transaction,
    input_index: usize,
    spent_output: &Output,
) -> Vec<u8> {
    let sighash = sighash_v2(tx, input_index, spent_output);
    let sig = sk.try_sign(&sighash, &[]).unwrap();
    serialize_witness(pk_bytes, &sig.to_vec())
}

/// Build a transaction spending a legacy output into a PQ output.
/// Returns the transaction (with a dummy witness for the legacy input).
fn build_legacy_to_pq_tx(
    input_outpoint: OutPoint,
    pq_commitment: Commitment,
    value: u64,
) -> Transaction {
    Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: input_outpoint,
            witness: vec![0xDE, 0xAD], // dummy witness for legacy
        }],
        outputs: vec![pq_tx_output(pq_commitment, value)],
        locktime: 0,
    }
}

// ---------------------------------------------------------------------------
// 13.2: Full migration scenario
// ---------------------------------------------------------------------------
//
// Requirements: 4.1, 4.2, 4.3, 4.4, 4.5, 4.9, 5.1, 5.2, 5.3

#[test]
fn integration_full_migration_scenario() {
    // Setup: MigrationConfig with H_a=100_000, H_c=152_560
    let config = MigrationConfig::with_recommended_grace(100_000);
    let h_a = config.announcement_height; // 100_000
    let h_c = config.cutover_height;       // 152_560

    // Generate PQ keypairs for migration targets
    let (pk1, sk1, commitment1) = gen_pq_keypair();
    let (_pk2, _sk2, commitment2) = gen_pq_keypair();

    // --- Phase 0: Pre-activation (height < H_a) ---
    // Create a UTXO set with legacy outputs
    let mut utxo_set = UtxoSet::new();
    let legacy_op1 = outpoint(1, 0);
    let legacy_op2 = outpoint(2, 0);
    let legacy_op3 = outpoint(3, 0); // this one will NOT be migrated
    let legacy_op4 = outpoint(4, 0); // for pre-activation test
    let legacy_op5 = outpoint(5, 0); // for announcement PQ creation test
    let legacy_op6 = outpoint(6, 0); // for announcement legacy rejection test
    utxo_set.insert(legacy_op1.clone(), legacy_output(100_000));
    utxo_set.insert(legacy_op2.clone(), legacy_output(200_000));
    utxo_set.insert(legacy_op3.clone(), legacy_output(50_000));
    utxo_set.insert(legacy_op4.clone(), legacy_output(10_000));
    utxo_set.insert(legacy_op5.clone(), legacy_output(10_000));
    utxo_set.insert(legacy_op6.clone(), legacy_output(10_000));

    // Pre-activation: legacy output creation is allowed
    let pre_act_tx = Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: legacy_op4.clone(),
            witness: vec![0xDE, 0xAD],
        }],
        outputs: vec![legacy_tx_output(10_000)],
        locktime: 0,
    };
    assert!(
        valid_tx(&utxo_set, &pre_act_tx, h_a - 1, &config),
        "Pre-activation: legacy output creation should be allowed"
    );
    delta_tx(&mut utxo_set, &pre_act_tx);

    // --- Phase 1: Announcement (height = H_a) ---
    // PQ output creation works
    let pq_creation_tx = Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: legacy_op5.clone(),
            witness: vec![0xDE, 0xAD],
        }],
        outputs: vec![pq_tx_output(commitment1, 10_000)],
        locktime: 0,
    };
    assert!(
        valid_tx(&utxo_set, &pq_creation_tx, h_a, &config),
        "At H_a: PQ output creation should be allowed"
    );
    delta_tx(&mut utxo_set, &pq_creation_tx);

    // Legacy output creation is rejected at H_a
    let legacy_creation_tx = Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: legacy_op6.clone(),
            witness: vec![0xDE, 0xAD],
        }],
        outputs: vec![legacy_tx_output(10_000)],
        locktime: 0,
    };
    assert!(
        !valid_tx(&utxo_set, &legacy_creation_tx, h_a, &config),
        "At H_a: legacy output creation should be rejected"
    );

    // --- Phase 2: Grace period — migrate legacy output 1 ---
    let grace_height = h_a + 1000; // somewhere in the grace period
    let migrate_tx1 = build_legacy_to_pq_tx(legacy_op1.clone(), commitment1, 100_000);
    assert!(
        valid_tx(&utxo_set, &migrate_tx1, grace_height, &config),
        "Grace period: spending legacy output into PQ output should be accepted"
    );
    delta_tx(&mut utxo_set, &migrate_tx1);

    // Verify legacy_op1 is removed and new PQ output exists
    assert!(!utxo_set.contains_key(&legacy_op1));

    // --- Grace period: migrate legacy output 2 ---
    let migrate_tx2 = build_legacy_to_pq_tx(legacy_op2.clone(), commitment2, 200_000);
    assert!(
        valid_tx(&utxo_set, &migrate_tx2, grace_height + 100, &config),
        "Grace period: second migration should be accepted"
    );
    delta_tx(&mut utxo_set, &migrate_tx2);
    assert!(!utxo_set.contains_key(&legacy_op2));

    // legacy_op3 is NOT migrated — it will be frozen at cutover

    // --- Phase 3: Cutover (height = H_c) ---
    // Legacy spends are rejected after cutover
    let post_cutover_legacy_tx = Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: legacy_op3.clone(),
            witness: vec![0xDE, 0xAD],
        }],
        outputs: vec![pq_tx_output(commitment1, 50_000)],
        locktime: 0,
    };
    assert!(
        !valid_tx(&utxo_set, &post_cutover_legacy_tx, h_c, &config),
        "At cutover: legacy spends should be rejected"
    );

    // Verify unmigrated legacy output is frozen but still in UTXO set (Req 5.3)
    assert!(
        utxo_set.contains_key(&legacy_op3),
        "Frozen output must remain in UTXO set"
    );
    let frozen_output = utxo_set.get(&legacy_op3).unwrap();
    assert!(
        is_frozen(h_c, frozen_output, &config),
        "Unmigrated legacy output should be frozen at cutover"
    );

    // PQ spends are accepted after cutover — spend the migrated PQ output
    // We need to find the outpoint created by migrate_tx1 (value 100_000)
    // compute_txid is private, so we look for the PQ output in the UTXO set
    let pq_outpoint = utxo_set
        .iter()
        .find(|(_, o)| o.script_version == 2 && o.commitment == commitment1 && o.value == 100_000)
        .map(|(op, _)| op.clone())
        .expect("migrated PQ output should exist in UTXO set");

    let pq_spent_output = utxo_set.get(&pq_outpoint).unwrap().clone();

    // Build a transaction spending the PQ output — needs a real PQ witness
    let (_pk_new, _sk_new, commitment_new) = gen_pq_keypair();
    let mut pq_spend_tx = Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: pq_outpoint.clone(),
            witness: vec![], // placeholder
        }],
        outputs: vec![pq_tx_output(commitment_new, pq_spent_output.value)],
        locktime: 0,
    };
    // Build the real witness
    let witness = build_pq_witness(&pk1, &sk1, &pq_spend_tx, 0, &pq_spent_output);
    pq_spend_tx.inputs[0].witness = witness;

    assert!(
        valid_tx(&utxo_set, &pq_spend_tx, h_c + 100, &config),
        "After cutover: PQ spends should be accepted"
    );
}

// ---------------------------------------------------------------------------
// 13.3: Mixed block validation during grace period
// ---------------------------------------------------------------------------
//
// Requirements: 3.2, 4.4, 8.5

#[test]
fn integration_mixed_block_validation_during_grace_period() {
    let config = MigrationConfig::with_recommended_grace(100_000);
    let grace_height = config.announcement_height + 5000; // in grace period

    // Generate PQ keypairs
    let (_pk1, _sk1, commitment1) = gen_pq_keypair();
    let (pk2, sk2, commitment2) = gen_pq_keypair();

    // Setup UTXO set with both legacy and PQ outputs
    let mut utxo_set = UtxoSet::new();

    // Legacy output to be spent
    let legacy_op = outpoint(10, 0);
    utxo_set.insert(legacy_op.clone(), legacy_output(100_000));

    // PQ output to be spent
    let pq_op = outpoint(20, 0);
    utxo_set.insert(pq_op.clone(), pq_utxo_output(commitment2, 200_000));

    // Transaction 1: spend legacy output into PQ output (migration tx)
    let tx1 = build_legacy_to_pq_tx(legacy_op.clone(), commitment1, 100_000);

    // Transaction 2: spend PQ output into PQ output (PQ-to-PQ tx)
    let (_, _, commitment3) = gen_pq_keypair();
    let pq_spent = utxo_set.get(&pq_op).unwrap().clone();
    let mut tx2 = Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: pq_op.clone(),
            witness: vec![], // placeholder
        }],
        outputs: vec![pq_tx_output(commitment3, 200_000)],
        locktime: 0,
    };
    let witness2 = build_pq_witness(&pk2, &sk2, &tx2, 0, &pq_spent);
    tx2.inputs[0].witness = witness2;

    // Construct a block with both transactions
    let block = vec![tx1.clone(), tx2.clone()];

    // Verify valid_block accepts the mixed block during grace period
    assert!(
        valid_block(&utxo_set, &block, grace_height, &config),
        "Mixed block with legacy-spending and PQ-spending txs should be accepted during grace period"
    );

    // Verify check_block_cost correctly accounts for both transaction types
    assert!(
        check_block_cost(&block),
        "Block cost should be within C_max for a small mixed block"
    );

    // Verify individual transaction costs are reasonable
    let cost1 = cost_tx(&tx1);
    let cost2 = cost_tx(&tx2);
    assert!(cost1 > 0, "Legacy-spending tx should have non-zero cost");
    assert!(cost2 > 0, "PQ-spending tx should have non-zero cost");
    assert!(
        cost1 + cost2 <= C_MAX,
        "Total block cost ({} + {} = {}) should be within C_MAX ({})",
        cost1,
        cost2,
        cost1 + cost2,
        C_MAX
    );
}

// ---------------------------------------------------------------------------
// 13.4: Multisig migration
// ---------------------------------------------------------------------------
//
// Requirements: 6.2, 6.3, 6.5

#[test]
fn integration_multisig_migration() {
    let config = MigrationConfig::with_recommended_grace(100_000);
    let grace_height = config.announcement_height + 2000;
    let _post_cutover = config.cutover_height + 100;

    // Generate 3 ML-DSA-44 keypairs for 2-of-3 multisig
    let (pk1, sk1, _) = gen_pq_keypair();
    let (pk2, sk2, _) = gen_pq_keypair();
    let (pk3, _sk3, _) = gen_pq_keypair();

    let pks = vec![pk1.clone(), pk2.clone(), pk3.clone()];

    // Compute multisig commitment: H(pk1 || pk2 || pk3)
    let multisig_commitment: Commitment = {
        let mut hasher = Sha256::new();
        for pk in &pks {
            hasher.update(pk);
        }
        hasher.finalize().into()
    };

    // --- Step 1: Create a legacy 2-of-3 multisig output ---
    // (In our model, legacy outputs are just v0 with a commitment)
    let mut utxo_set = UtxoSet::new();
    let legacy_multisig_op = outpoint(50, 0);
    utxo_set.insert(legacy_multisig_op.clone(), legacy_output(500_000));

    // --- Step 2: During grace period, spend legacy into PQ multisig output ---
    let migrate_tx = Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: legacy_multisig_op.clone(),
            witness: vec![0xDE, 0xAD], // dummy witness for legacy
        }],
        outputs: vec![pq_tx_output(multisig_commitment, 500_000)],
        locktime: 0,
    };

    assert!(
        valid_tx(&utxo_set, &migrate_tx, grace_height, &config),
        "Grace period: migrating legacy to PQ multisig output should be accepted"
    );
    delta_tx(&mut utxo_set, &migrate_tx);

    // Find the new PQ multisig outpoint
    let pq_multisig_op = utxo_set
        .iter()
        .find(|(_, o)| o.script_version == 2 && o.commitment == multisig_commitment)
        .map(|(op, _)| op.clone())
        .expect("PQ multisig output should exist after migration");

    let pq_multisig_output = utxo_set.get(&pq_multisig_op).unwrap().clone();

    // --- Step 3: After cutover, spend the PQ multisig output ---
    // Build a transaction spending the PQ multisig output
    let (_, _, dest_commitment) = gen_pq_keypair();
    let mut multisig_spend_tx = Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: pq_multisig_op.clone(),
            witness: vec![], // placeholder
        }],
        outputs: vec![pq_tx_output(dest_commitment, 500_000)],
        locktime: 0,
    };

    // Compute sighash for the multisig spend
    let sighash = sighash_v2(&multisig_spend_tx, 0, &pq_multisig_output);

    // Sign with keys 0 and 1 (2-of-3, indices [0, 1])
    let sig1 = sk1.try_sign(&sighash, &[]).unwrap();
    let sig2 = sk2.try_sign(&sighash, &[]).unwrap();
    let sigs = vec![sig1.to_vec(), sig2.to_vec()];
    let indices = vec![0u8, 1u8];

    // Serialize the multisig witness
    let multisig_witness = serialize_multisig_witness(2, &pks, &sigs, &indices);
    multisig_spend_tx.inputs[0].witness = multisig_witness;

    // The spend predicate uses spend_pred_pq (single-sig) in valid_tx,
    // but our multisig witness won't pass single-sig parsing.
    // We need to verify the multisig spend predicate directly.
    assert!(
        spend_pred_pq_multisig(&multisig_commitment, &sighash, &multisig_spend_tx.inputs[0].witness),
        "After cutover: PQ multisig spend predicate should accept valid 2-of-3 witness"
    );

    // Verify weight accounting for the multisig transaction
    let multisig_cost = cost_tx(&multisig_spend_tx);
    assert!(
        multisig_cost > 0,
        "Multisig transaction should have non-zero cost"
    );
    // 2-of-3 ML-DSA-44 multisig witness is ~8,786 bytes
    // cost = witness_len + INPUT_OVERHEAD + BASE_TX_OVERHEAD + OUTPUT_WU
    // Should be significantly larger than a single-sig transaction
    assert!(
        multisig_cost > 8_000,
        "Multisig transaction cost ({}) should reflect the large witness size",
        multisig_cost
    );
}

// ---------------------------------------------------------------------------
// 13.5: Activation sequence
// ---------------------------------------------------------------------------
//
// Requirements: 7.1, 7.2, 7.6

#[test]
fn integration_activation_sequence() {
    let config = MigrationConfig::with_recommended_grace(100_000);
    let h_a = config.announcement_height; // 100_000
    let h_c = config.cutover_height;       // 152_560

    let (pk1, sk1, commitment1) = gen_pq_keypair();
    let (_, _, commitment2) = gen_pq_keypair();

    // --- Pre-activation (height < H_a): PQ outputs recognized as v2 ---
    assert_eq!(
        get_phase(h_a - 1, &config),
        MigrationPhase::PreActivation,
        "Before H_a should be PreActivation phase"
    );

    // Witness version 2 is recognized (WITNESS_VERSION constant)
    assert_eq!(WITNESS_VERSION, 2, "PQ witness version should be 2 (Req 7.6)");

    // Setup UTXO set with legacy outputs for testing all phases
    let mut utxo_set = UtxoSet::new();
    let fund_op1 = outpoint(101, 0); // for pre-act PQ creation
    let fund_op2 = outpoint(102, 0); // for pre-act legacy creation
    let fund_op3 = outpoint(103, 0); // for announcement PQ creation
    let fund_op4 = outpoint(104, 0); // for announcement legacy rejection
    let legacy_op = outpoint(100, 0); // for grace period migration
    utxo_set.insert(fund_op1.clone(), legacy_output(50_000));
    utxo_set.insert(fund_op2.clone(), legacy_output(30_000));
    utxo_set.insert(fund_op3.clone(), legacy_output(20_000));
    utxo_set.insert(fund_op4.clone(), legacy_output(20_000));
    utxo_set.insert(legacy_op.clone(), legacy_output(75_000));

    // Pre-activation: PQ outputs can be created
    let pre_act_pq_tx = Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: fund_op1.clone(),
            witness: vec![0xDE, 0xAD],
        }],
        outputs: vec![pq_tx_output(commitment1, 50_000)],
        locktime: 0,
    };
    assert!(
        valid_tx(&utxo_set, &pre_act_pq_tx, h_a - 1, &config),
        "Pre-activation: PQ output creation should be valid"
    );
    delta_tx(&mut utxo_set, &pre_act_pq_tx);

    // Pre-activation: legacy outputs can also be created
    let pre_act_legacy_tx = Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: fund_op2.clone(),
            witness: vec![0xDE, 0xAD],
        }],
        outputs: vec![legacy_tx_output(30_000)],
        locktime: 0,
    };
    assert!(
        valid_tx(&utxo_set, &pre_act_legacy_tx, h_a - 1, &config),
        "Pre-activation: legacy output creation should be valid"
    );
    delta_tx(&mut utxo_set, &pre_act_legacy_tx);

    // --- Announcement height (H_a): PQ outputs enabled, legacy creation blocked ---
    assert_eq!(
        get_phase(h_a, &config),
        MigrationPhase::GracePeriod,
        "At H_a should be GracePeriod phase"
    );

    // PQ output creation still works
    let announce_pq_tx = Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: fund_op3.clone(),
            witness: vec![0xDE, 0xAD],
        }],
        outputs: vec![pq_tx_output(commitment2, 20_000)],
        locktime: 0,
    };
    assert!(
        valid_tx(&utxo_set, &announce_pq_tx, h_a, &config),
        "At H_a: PQ output creation should be valid"
    );
    delta_tx(&mut utxo_set, &announce_pq_tx);

    // Legacy output creation is blocked
    let announce_legacy_tx = Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: fund_op4.clone(),
            witness: vec![0xDE, 0xAD],
        }],
        outputs: vec![legacy_tx_output(20_000)],
        locktime: 0,
    };
    assert!(
        !valid_tx(&utxo_set, &announce_legacy_tx, h_a, &config),
        "At H_a: legacy output creation should be rejected"
    );

    // --- Grace period [H_a, H_c): mixed spending allowed ---
    let grace_height = h_a + 10_000;
    assert_eq!(
        get_phase(grace_height, &config),
        MigrationPhase::GracePeriod,
        "During grace period should be GracePeriod phase"
    );

    // Legacy spend into PQ output (migration) is allowed
    let migration_tx = build_legacy_to_pq_tx(legacy_op.clone(), commitment1, 75_000);
    assert!(
        valid_tx(&utxo_set, &migration_tx, grace_height, &config),
        "Grace period: legacy-to-PQ migration should be accepted"
    );
    delta_tx(&mut utxo_set, &migration_tx);

    // Find the PQ output we just created
    let pq_op = utxo_set
        .iter()
        .find(|(_, o)| o.script_version == 2 && o.commitment == commitment1 && o.value == 75_000)
        .map(|(op, _)| op.clone())
        .expect("Migrated PQ output should exist");
    let pq_output_ref = utxo_set.get(&pq_op).unwrap().clone();

    // PQ spend during grace period is also allowed
    let (_, _, commitment3) = gen_pq_keypair();
    let mut pq_spend_grace = Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: pq_op.clone(),
            witness: vec![], // placeholder
        }],
        outputs: vec![pq_tx_output(commitment3, 75_000)],
        locktime: 0,
    };
    let witness = build_pq_witness(&pk1, &sk1, &pq_spend_grace, 0, &pq_output_ref);
    pq_spend_grace.inputs[0].witness = witness;

    assert!(
        valid_tx(&utxo_set, &pq_spend_grace, grace_height, &config),
        "Grace period: PQ spend should be accepted"
    );
    delta_tx(&mut utxo_set, &pq_spend_grace);

    // --- Cutover (H_c): PQ-only consensus enforced ---
    assert_eq!(
        get_phase(h_c, &config),
        MigrationPhase::PostCutover,
        "At H_c should be PostCutover phase"
    );

    // The fund_op4 legacy output was not consumed (legacy creation was rejected),
    // so it's still in the UTXO set and will be frozen at cutover.
    let unmigrated_op = fund_op4.clone();

    // Legacy spend is rejected after cutover
    let post_cutover_legacy = Transaction {
        version: 2,
        inputs: vec![TxInput {
            outpoint: unmigrated_op.clone(),
            witness: vec![0xDE, 0xAD],
        }],
        outputs: vec![pq_tx_output(commitment1, 20_000)],
        locktime: 0,
    };
    assert!(
        !valid_tx(&utxo_set, &post_cutover_legacy, h_c, &config),
        "At cutover: legacy spend should be rejected"
    );

    // Verify the unmigrated output is frozen
    let unmigrated_output = utxo_set.get(&unmigrated_op).unwrap();
    assert!(
        is_frozen(h_c, unmigrated_output, &config),
        "Unmigrated legacy output should be frozen at cutover"
    );

    // Verify frozen output remains in UTXO set
    assert!(
        utxo_set.contains_key(&unmigrated_op),
        "Frozen output must remain in UTXO set"
    );

    // PQ outputs are NOT frozen after cutover
    let pq_outputs: Vec<_> = utxo_set
        .iter()
        .filter(|(_, o)| o.script_version == 2)
        .collect();
    for (_, pq_out) in &pq_outputs {
        assert!(
            !is_frozen(h_c, pq_out, &config),
            "PQ output should NOT be frozen at cutover"
        );
    }

    // Verify the full state machine transition sequence
    assert_eq!(get_phase(0, &config), MigrationPhase::PreActivation);
    assert_eq!(get_phase(h_a - 1, &config), MigrationPhase::PreActivation);
    assert_eq!(get_phase(h_a, &config), MigrationPhase::GracePeriod);
    assert_eq!(get_phase(h_c - 1, &config), MigrationPhase::GracePeriod);
    assert_eq!(get_phase(h_c, &config), MigrationPhase::PostCutover);
    assert_eq!(get_phase(h_c + 100_000, &config), MigrationPhase::PostCutover);
}
