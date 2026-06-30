#!/usr/bin/env bash
# build_extraction.sh: Build script for Coq→OCaml extraction
#
# This script:
# 1. Compiles all Coq modules in the correct order
# 2. Generates OCaml extraction from WitnessExtraction.v, SighashExtraction.v,
#    TxidExtraction.v, and TransitionExtraction.v
# 3. Compiles the extracted OCaml code and vector harness
# 4. Runs the golden vector generator
# 5. Compares with Rust implementation
#
# Copyright (c) 2026 Mayckon Giovani. MIT License.

set -e  # Exit on error

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/formal/coq"

echo "=========================================="
echo "Building Coq Proofs and Extraction"
echo "=========================================="

# Step 1: Compile base modules first
echo "[1/5] Compiling base Coq modules..."
coqc -Q . BitcoinPQ VarintConcrete.v
coqc -Q . BitcoinPQ SpendPredPQ.v
coqc -Q . BitcoinPQ UTXOTransitions.v
coqc -Q . BitcoinPQ SighashV2.v
coqc -Q . BitcoinPQ TxidPreimage.v

echo "[2/5] Base modules compiled successfully"

# Step 2: Compile extraction module (it imports from parent)
echo "[3/5] Compiling extraction module..."
cd extraction
coqc -Q .. BitcoinPQ -I .. WitnessExtraction.v
coqc -Q .. BitcoinPQ -I .. SighashExtraction.v
coqc -Q .. BitcoinPQ -I .. TxidExtraction.v
coqc -Q .. BitcoinPQ -I .. TransitionExtraction.v

echo "[4/5] Extraction module compiled"

# Step 3: Extract to OCaml
echo "[5/5] Extracting to OCaml..."
coqc -Q .. BitcoinPQ ExtractWitnessVectors.v
coqc -Q .. BitcoinPQ ExtractSighashVectors.v
coqc -Q .. BitcoinPQ ExtractTxidVectors.v
coqc -Q .. BitcoinPQ ExtractTransitionVectors.v

echo "=========================================="
echo "Coq→OCaml Extraction Complete"
echo "=========================================="

# Step 4: Compile OCaml code
echo "Compiling OCaml golden vector generator..."
ocamlc -c golden_vectors_extracted.mli golden_vectors_extracted.ml
ocamlc -c sighash_extracted.mli sighash_extracted.ml
ocamlc -c txid_extracted.mli txid_extracted.ml
ocamlc -c transition_extracted.mli transition_extracted.ml
ocamlc -o golden_vectors golden_vectors_extracted.cmo golden_vectors.ml
ocamlc -o varint_refinement golden_vectors_extracted.cmo varint_refinement.ml
ocamlc -o witness_refinement golden_vectors_extracted.cmo witness_refinement.ml
ocamlc -o sighash_refinement sighash_extracted.cmo sighash_refinement.ml
ocamlc -o txid_refinement txid_extracted.cmo txid_refinement.ml
ocamlc -o transition_refinement transition_extracted.cmo transition_refinement.ml

echo "Running golden vector generator..."
./golden_vectors > coq_vectors.json

echo "Golden vectors generated: coq_vectors.json"
echo "Running Coq-extracted varint refinement summary..."
./varint_refinement > coq_varint_refinement.json
echo "Running Coq-extracted witness refinement summary..."
./witness_refinement > coq_witness_refinement.json
echo "Running Coq-extracted sighash transcript refinement summary..."
./sighash_refinement > coq_sighash_refinement.json
echo "Running Coq-extracted txid preimage refinement summary..."
./txid_refinement > coq_txid_refinement.json
echo "Running Coq-extracted transition refinement summary..."
./transition_refinement > coq_transition_refinement.json

# Step 5: Return to project root and generate Rust vectors
cd "$SCRIPT_DIR"
echo "Generating Rust golden vectors..."
cargo run --example generate_golden_vectors > rust_vectors.json
echo "Generating Rust varint refinement summary..."
cargo run --example generate_varint_refinement > rust_varint_refinement.json
echo "Generating Rust witness refinement summary..."
cargo run --example generate_witness_refinement > rust_witness_refinement.json
echo "Generating Rust sighash transcript refinement summary..."
cargo run --example generate_sighash_refinement > rust_sighash_refinement.json
echo "Generating Rust txid preimage refinement summary..."
cargo run --example generate_txid_refinement > rust_txid_refinement.json
echo "Generating Rust transition refinement summary..."
cargo run --example generate_transition_refinement > rust_transition_refinement.json

# Step 6: Compare
echo "=========================================="
echo "Comparing Coq vs Rust vectors..."
echo "=========================================="

python3 << 'PYEOF'
import json
import sys

try:
    with open('formal/coq/extraction/coq_vectors.json', 'r') as f:
        coq_data = json.load(f)
except FileNotFoundError:
    print("ERROR: Coq vectors not found. Did extraction succeed?")
    sys.exit(1)

try:
    with open('rust_vectors.json', 'r') as f:
        rust_data = json.load(f)
except FileNotFoundError:
    print("ERROR: Rust vectors not found.")
    sys.exit(1)

try:
    with open('formal/coq/extraction/coq_varint_refinement.json', 'r') as f:
        coq_varint = json.load(f)
except FileNotFoundError:
    print("ERROR: Coq varint refinement summary not found.")
    sys.exit(1)

try:
    with open('rust_varint_refinement.json', 'r') as f:
        rust_varint = json.load(f)
except FileNotFoundError:
    print("ERROR: Rust varint refinement summary not found.")
    sys.exit(1)

try:
    with open('formal/coq/extraction/coq_witness_refinement.json', 'r') as f:
        coq_witness = json.load(f)
except FileNotFoundError:
    print("ERROR: Coq witness refinement summary not found.")
    sys.exit(1)

try:
    with open('rust_witness_refinement.json', 'r') as f:
        rust_witness = json.load(f)
except FileNotFoundError:
    print("ERROR: Rust witness refinement summary not found.")
    sys.exit(1)

try:
    with open('formal/coq/extraction/coq_sighash_refinement.json', 'r') as f:
        coq_sighash = json.load(f)
except FileNotFoundError:
    print("ERROR: Coq sighash refinement summary not found.")
    sys.exit(1)

try:
    with open('rust_sighash_refinement.json', 'r') as f:
        rust_sighash = json.load(f)
except FileNotFoundError:
    print("ERROR: Rust sighash refinement summary not found.")
    sys.exit(1)

try:
    with open('formal/coq/extraction/coq_txid_refinement.json', 'r') as f:
        coq_txid = json.load(f)
except FileNotFoundError:
    print("ERROR: Coq txid refinement summary not found.")
    sys.exit(1)

try:
    with open('rust_txid_refinement.json', 'r') as f:
        rust_txid = json.load(f)
except FileNotFoundError:
    print("ERROR: Rust txid refinement summary not found.")
    sys.exit(1)

try:
    with open('formal/coq/extraction/coq_transition_refinement.json', 'r') as f:
        coq_transition = json.load(f)
except FileNotFoundError:
    print("ERROR: Coq transition refinement summary not found.")
    sys.exit(1)

try:
    with open('rust_transition_refinement.json', 'r') as f:
        rust_transition = json.load(f)
except FileNotFoundError:
    print("ERROR: Rust transition refinement summary not found.")
    sys.exit(1)

print(f"Coq vectors: {len(coq_data)} test cases")
print(f"Rust vectors: {len(rust_data)} test cases")

# Build lookup by name
coq_by_name = {v['name']: v for v in coq_data}
rust_by_name = {v['name']: v for v in rust_data}

mismatches = []
missing = []
unexpected = []

for name in coq_by_name:
    if name not in rust_by_name:
        missing.append(f"Rust missing: {name}")
        continue

    coq_vec = coq_by_name[name]
    rust_vec = rust_by_name[name]

    if coq_vec['pk_len'] != rust_vec['pk_len']:
        mismatches.append(f"{name}: pk_len mismatch - Coq:{coq_vec['pk_len']} vs Rust:{rust_vec['pk_len']}")

    if coq_vec['sig_len'] != rust_vec['sig_len']:
        mismatches.append(f"{name}: sig_len mismatch - Coq:{coq_vec['sig_len']} vs Rust:{rust_vec['sig_len']}")

    # Compare witness (the critical check)
    if coq_vec['witness'] != rust_vec['witness']:
        mismatches.append(f"{name}: WITNESS MISMATCH")
        mismatches.append(f"  Coq:  {coq_vec['witness'][:60]}...")
        mismatches.append(f"  Rust: {rust_vec['witness'][:60]}...")

for name in rust_by_name:
    if name not in coq_by_name:
        unexpected.append(f"Unexpected Rust vector: {name}")

if missing:
    print("\n=== MISSING VECTORS ===")
    for m in missing:
        print(m)

if unexpected:
    print("\n=== UNEXPECTED VECTORS ===")
    for u in unexpected:
        print(u)

if mismatches or missing or unexpected:
    print("\n=== MISMATCHES FOUND ===")
    for m in mismatches:
        print(m)
    sys.exit(1)

if coq_varint != rust_varint:
    print("\n=== VARINT REFINEMENT MISMATCH ===")
    print(f"Coq:  {coq_varint}")
    print(f"Rust: {rust_varint}")
    sys.exit(1)

if coq_witness != rust_witness:
    print("\n=== WITNESS REFINEMENT MISMATCH ===")
    print(f"Coq:  {coq_witness}")
    print(f"Rust: {rust_witness}")
    sys.exit(1)

if coq_sighash != rust_sighash:
    print("\n=== SIGHASH TRANSCRIPT REFINEMENT MISMATCH ===")
    print(f"Coq:  {coq_sighash}")
    print(f"Rust: {rust_sighash}")
    sys.exit(1)

if coq_txid != rust_txid:
    print("\n=== TXID PREIMAGE REFINEMENT MISMATCH ===")
    print(f"Coq:  {coq_txid}")
    print(f"Rust: {rust_txid}")
    sys.exit(1)

if coq_transition != rust_transition:
    print("\n=== TRANSITION REFINEMENT MISMATCH ===")
    print(f"Coq:  {coq_transition}")
    print(f"Rust: {rust_transition}")
    sys.exit(1)

print("\n=== SUCCESS ===")
print("All bounded vectors match byte-for-byte!")
print("Exhaustive u16 varint refinement summaries match!")
print("Witness parser/serializer/consensus-domain/trace refinement summaries match!")
print("Sighash transcript refinement summaries match!")
print("Txid preimage refinement summaries match!")
print("UTXO transition refinement summaries match!")
print("PO-8: bounded Coq witness model ↔ Rust encoding implementation extraction-boundary evidence")
print("PO-4: Coq sighash transcript model ↔ Rust preimage serialization evidence")
print("PO-5: Coq txid/UTXO transition model ↔ Rust implementation extraction-boundary evidence")
PYEOF

echo ""
echo "=========================================="
echo "Build Complete!"
echo "=========================================="
echo ""
echo "Artifacts generated:"
echo "  - formal/coq/extraction/coq_vectors.json"
echo "  - rust_vectors.json"
echo "  - formal/coq/extraction/coq_varint_refinement.json"
echo "  - rust_varint_refinement.json"
echo "  - formal/coq/extraction/coq_witness_refinement.json"
echo "  - rust_witness_refinement.json"
echo "  - formal/coq/extraction/coq_sighash_refinement.json"
echo "  - rust_sighash_refinement.json"
echo "  - formal/coq/extraction/coq_txid_refinement.json"
echo "  - rust_txid_refinement.json"
echo "  - formal/coq/extraction/coq_transition_refinement.json"
echo "  - rust_transition_refinement.json"
echo ""
echo "Proof Obligations Status:"
echo "  PO-1 (Totality):          VERIFIED"
echo "  PO-2 (Determinism):       VERIFIED"
echo "  PO-3 (Parse Canonicality): VERIFIED"
echo "  PO-4 (Sighash Commitment): VERIFIED MODEL (SighashV2.v + Rust PBT)"
echo "  PO-4 (Rust transcript):     COQ-EXTRACTED VS RUST PREIMAGE SERIALIZATION REFINEMENT"
echo "  PO-4 (Compiled artifact):   RUN ./verify_sighash_refinement.sh FOR RELEASE-BINARY TRANSCRIPT VALIDATION"
echo "  PO-5 (Txid preimage):      COQ-EXTRACTED VS RUST TXID PREIMAGE REFINEMENT"
echo "  PO-5 (Transition Det.):    VERIFIED MODEL + RUST TRANSITION REFINEMENT EVIDENCE"
echo "  PO-5 (Txid compiled):      RUN ./verify_txid_refinement.sh FOR RELEASE-BINARY TXID PREIMAGE VALIDATION"
echo "  PO-5 (Compiled artifact):  RUN ./verify_transition_refinement.sh FOR RELEASE-BINARY TRANSITION VALIDATION"
echo "  PO-7 (Cost Boundedness):   VERIFIED"
echo "  PO-8 (Correspondence):     BOUNDED EXTRACTION EVIDENCE + CONCRETE CANONICALITY + EXHAUSTIVE VARINT + CONSENSUS WITNESS REFINEMENT (<= u16)"
echo "  PO-8 (Rust source):        RUN ./verify_source_refinement.sh FOR KANI SOURCE-LEVEL BOUNDED REFINEMENT"
echo "  PO-8 (Compiled artifact):  RUN ./verify_compiled_refinement.sh FOR RELEASE-BINARY TRANSLATION VALIDATION"
echo ""
