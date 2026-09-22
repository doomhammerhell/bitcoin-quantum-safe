#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
source "$SCRIPT_DIR/rust_toolchain.sh"
OUT_DIR="${TRANSITION_INVARIANT_REFINEMENT_OUT_DIR:-$ROOT_DIR/target/transition-invariant-refinement}"
if [[ "$OUT_DIR" != /* ]]; then
  OUT_DIR="$ROOT_DIR/$OUT_DIR"
fi

cd "$ROOT_DIR"
mkdir -p "$OUT_DIR"

require_file() {
  local primary="$1"
  local fallback="$2"
  local label="$3"

  if [[ -f "$primary" ]]; then
    printf '%s\n' "$primary"
    return 0
  fi

  if [[ -f "$fallback" ]]; then
    printf '%s\n' "$fallback"
    return 0
  fi

  echo "missing $label; run 'opam exec -- bash ./scripts/verification/build_extraction.sh' or download the Coq CI artifact first" >&2
  exit 1
}

COQ_TRANSITION_INVARIANT="$(require_file "formal/coq/extraction/coq_transition_invariant_refinement.json" "coq_transition_invariant_refinement.json" "Coq transition invariant refinement witnesses")"
RUST_TRANSITION_INVARIANT="$OUT_DIR/rust_transition_invariant_refinement.release.json"
CERTIFICATE="$OUT_DIR/transition_invariant_refinement_certificate.json"

echo "Building release transition invariant refinement executable..."
cargo build --release --example generate_transition_invariant_refinement

"$ROOT_DIR/target/release/examples/generate_transition_invariant_refinement" > "$RUST_TRANSITION_INVARIANT"

python3 - "$COQ_TRANSITION_INVARIANT" "$RUST_TRANSITION_INVARIANT" "$CERTIFICATE" "$ROOT_DIR" <<'PY'
import hashlib
import json
import os
import platform
import subprocess
import sys
from pathlib import Path

coq_transition_invariant_path, rust_transition_invariant_path, certificate_path, root_dir = sys.argv[1:]
root = Path(root_dir)


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


coq_value = load_json(coq_transition_invariant_path)
rust_value = load_json(rust_transition_invariant_path)

compare_result = subprocess.run(
    [
        sys.executable,
        str(root / "scripts/verification/compare_transition_invariant_refinement.py"),
        coq_transition_invariant_path,
        rust_transition_invariant_path,
    ],
    cwd=root,
)
if compare_result.returncode != 0:
    sys.exit(compare_result.returncode)


def command_output(*args):
    return subprocess.check_output(args, cwd=root, text=True).strip()


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def relpath(path):
    return os.path.relpath(path, root)


tracked_inputs = [
    "Cargo.lock",
    "Cargo.toml",
    "src/lib.rs",
    "src/transition_core.rs",
    "src/types.rs",
    "src/migration.rs",
    "src/freeze.rs",
    "src/weight.rs",
    "src/params.rs",
    "formal/coq/UTXOTransitions.v",
    "formal/coq/extraction/TransitionExtraction.v",
    "formal/coq/extraction/ExtractTransitionVectors.v",
    "formal/coq/extraction/transition_invariant_refinement.ml",
    "examples/generate_transition_invariant_refinement.rs",
    "scripts/verification/compare_transition_invariant_refinement.py",
    "scripts/verification/verify_transition_invariant_refinement.sh",
]

release_binary = root / "target/release/examples/generate_transition_invariant_refinement"
generated_output = Path(rust_transition_invariant_path)
coq_applicable_cases = [
    case
    for case in coq_value.get("cases", [])
    if case.get("theorem", {}).get("applicable") is True
]
coq_value_applicable_cases = [
    case
    for case in coq_value.get("cases", [])
    if case.get("value_theorem", {}).get("applicable") is True
]
coq_migration_applicable_cases = [
    case
    for case in coq_value.get("cases", [])
    if case.get("migration_theorem", {}).get("applicable") is True
]
coq_freeze_applicable_cases = [
    case
    for case in coq_value.get("cases", [])
    if case.get("freeze_theorem", {}).get("applicable") is True
]
coq_frozen_count_applicable_cases = [
    case
    for case in coq_value.get("cases", [])
    if case.get("frozen_count_theorem", {}).get("applicable") is True
]
coq_boundary_cases = [
    case
    for case in coq_value.get("cases", [])
    if case.get("preconditions", {}).get("fresh_id_assumption_holds") is False
]

certificate = {
    "validation": "PO-6 structural UTXO-domain/value/migration/freeze invariant refinement validation",
    "scope": {
        "claim": "release binary observing Rust structural final-state invariant witnesses produces the same per-case UTXO-domain preservation, total-value non-increase, legacy-output non-increase after announcement, PQ-only accepted-input behavior after cutover, and frozen-count non-increase evidence as the Coq-extracted invariant harness under each theorem's explicit boundary",
        "non_claim": "this is not a proof of SHA-256 txid collision resistance, UTXO-store backend internals, cryptographic witness verification, rustc, LLVM, linker, CPU, or OS correctness",
    },
    "evidence": {
        "format": "per-case-structured-invariant-witnesses",
        "semantic_diff_tool": "scripts/verification/compare_transition_invariant_refinement.py",
        "case_count": len(coq_value.get("cases", [])),
        "domain_theorem_applicable_case_count": len(coq_applicable_cases),
        "value_theorem_applicable_case_count": len(coq_value_applicable_cases),
        "migration_theorem_applicable_case_count": len(coq_migration_applicable_cases),
        "freeze_theorem_applicable_case_count": len(coq_freeze_applicable_cases),
        "frozen_count_theorem_applicable_case_count": len(coq_frozen_count_applicable_cases),
        "freshness_boundary_case_count": len(coq_boundary_cases),
    },
    "domain_theorem_boundary": {
        "coq_theorem": "apply_valid_block_structural_preserves_domain_nodup",
        "precondition": "NoDup (utxo_domain U) / domain_below U fresh_id / apply_valid_block_structural U block height cfg fresh_id = Some U'",
        "conclusion": "NoDup (utxo_domain U') and domain_below U' (fresh_id + block_output_count block)",
        "freshness_boundary": "cases with false fresh_id_assumption_holds are explicit non-applicability witnesses, not theorem-covered executions",
    },
    "value_theorem_boundary": {
        "coq_theorem": "apply_valid_block_structural_preserves_total_value",
        "precondition": "NoDup (utxo_domain U) / domain_below U fresh_id / apply_valid_block_structural U block height cfg fresh_id = Some U'",
        "conclusion": "utxo_total_value U' <= utxo_total_value U",
        "economic_scope": "non-increase of total UTXO value; exact fee accounting and monetary-supply policy are outside this structural theorem",
    },
    "migration_theorem_boundary": {
        "coq_theorem": "apply_valid_block_structural_legacy_count_nonincreasing_after_announcement",
        "precondition": "announcement_height cfg <= height / apply_valid_block_structural U block height cfg fresh_id = Some U'",
        "conclusion": "legacy_utxo_count U' <= legacy_utxo_count U",
        "scope": "legacy/taproot-like script versions are all non-PQ script versions in the structural model",
    },
    "freeze_theorem_boundary": {
        "coq_theorem": "apply_valid_block_structural_inputs_pq_after_cutover",
        "precondition": "cutover_height cfg <= height / apply_valid_block_structural U block height cfg fresh_id = Some U'",
        "conclusion": "accepted_block_inputs_pq_or_missing U block height cfg fresh_id = true",
        "scope": "missing inputs are ignored by the freeze predicate because structural validity rejects them earlier",
    },
    "frozen_count_theorem_boundary": {
        "coq_theorem": "apply_valid_block_structural_frozen_count_nonincreasing_after_cutover",
        "precondition": "announcement_height cfg <= cutover_height cfg / cutover_height cfg <= height / apply_valid_block_structural U block height cfg fresh_id = Some U'",
        "conclusion": "frozen_utxo_count height cfg U' <= frozen_utxo_count height cfg U",
        "scope": "structural frozen-count non-increase; cryptographic witness validity remains a separate consensus-path obligation",
    },
    "projection": {
        "coq": "association-list UTXO indexed by abstract nat outpoint IDs",
        "rust": "UtxoSet/UtxoStore UTXO indexed by synthetic OutPoint values; fresh IDs are mapped to compute_txid(tx), vout when the theorem precondition permits observation",
    },
    "toolchain": {
        "rustc": command_output("rustc", "-Vv"),
        "cargo": command_output("cargo", "-Vv"),
        "host": platform.platform(),
    },
    "inputs": {path: sha256(root / path) for path in tracked_inputs if (root / path).exists()},
    "release_binary": {relpath(release_binary): sha256(release_binary)},
    "generated_output": {relpath(generated_output): sha256(generated_output)},
    "comparison": "match",
}

with open(certificate_path, "w", encoding="utf-8") as handle:
    json.dump(certificate, handle, indent=2, sort_keys=True)
    handle.write("\n")

print("=== SUCCESS ===")
print("Compiled transition invariant refinement binary matches Coq-extracted PO-6 domain/value/migration/freeze invariant witnesses.")
print(f"Certificate: {certificate_path}")
PY
