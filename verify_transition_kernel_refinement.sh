#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR="${TRANSITION_KERNEL_REFINEMENT_OUT_DIR:-$ROOT_DIR/target/transition-kernel-refinement}"
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

  echo "missing $label; run 'opam exec -- bash ./build_extraction.sh' or download the Coq CI artifact first" >&2
  exit 1
}

COQ_TRANSITION_KERNEL="$(require_file "formal/coq/extraction/coq_transition_kernel_refinement.json" "coq_transition_kernel_refinement.json" "Coq transition-kernel refinement witnesses")"
RUST_TRANSITION_KERNEL="$OUT_DIR/rust_transition_kernel_refinement.release.json"
CERTIFICATE="$OUT_DIR/transition_kernel_refinement_certificate.json"

echo "Building release transition-kernel refinement executable..."
cargo build --release --example generate_transition_kernel_refinement

"$ROOT_DIR/target/release/examples/generate_transition_kernel_refinement" > "$RUST_TRANSITION_KERNEL"

python3 - "$COQ_TRANSITION_KERNEL" "$RUST_TRANSITION_KERNEL" "$CERTIFICATE" "$ROOT_DIR" <<'PY'
import hashlib
import json
import platform
import subprocess
import sys
from pathlib import Path

coq_transition_kernel_path, rust_transition_kernel_path, certificate_path, root_dir = sys.argv[1:]
root = Path(root_dir)


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


coq_value = load_json(coq_transition_kernel_path)
rust_value = load_json(rust_transition_kernel_path)

compare_result = subprocess.run(
    [
        sys.executable,
        str(root / "compare_transition_kernel_refinement.py"),
        coq_transition_kernel_path,
        rust_transition_kernel_path,
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
    "formal/coq/extraction/transition_kernel_refinement.ml",
    "examples/generate_transition_kernel_refinement.rs",
    "compare_transition_kernel_refinement.py",
]

release_binary = "target/release/examples/generate_transition_kernel_refinement"
generated_output = Path(rust_transition_kernel_path).relative_to(root)

certificate = {
    "validation": "PO-5 transition-kernel adapter report refinement validation",
    "scope": {
        "claim": "release binary observing Rust DeployedTransitionKernel reports produces the same per-case StructuralTxReport and StructuralBlockReport witnesses as the CoqExtractedTransitionKernel oracle over the deterministic projection matrix",
        "non_claim": "this is not a proof of SHA-256 txid collision resistance, UTXO-store backend internals, cryptographic witness verification, rustc, LLVM, linker, CPU, or OS correctness",
    },
    "evidence": {
        "format": "per-case-structured-witnesses",
        "semantic_diff_tool": "compare_transition_kernel_refinement.py",
        "transaction_cases": len(coq_value.get("cases", {}).get("transactions", [])),
        "block_cases": len(coq_value.get("cases", {}).get("blocks", [])),
    },
    "projection": {
        "coq": "association-list UTXO indexed by abstract nat outpoint IDs",
        "rust": "UtxoSet/UtxoStore UTXO indexed by synthetic OutPoint values; fresh IDs are mapped to compute_txid(tx), vout",
    },
    "adapter_boundary": {
        "coq_oracle": "CoqExtractedTransitionKernel",
        "rust_adapter": "DeployedTransitionKernel",
        "observed_reports": ["StructuralTxReport", "StructuralBlockReport"],
    },
    "toolchain": {
        "rustc": command_output("rustc", "-Vv"),
        "cargo": command_output("cargo", "-Vv"),
        "host": platform.platform(),
    },
    "inputs": {path: sha256(root / path) for path in tracked_inputs if (root / path).exists()},
    "release_binary": {release_binary: sha256(root / release_binary)},
    "generated_output": {str(generated_output): sha256(root / generated_output)},
    "comparison": "match",
}

with open(certificate_path, "w", encoding="utf-8") as handle:
    json.dump(certificate, handle, indent=2, sort_keys=True)
    handle.write("\n")

print("=== SUCCESS ===")
print("Compiled transition-kernel refinement binary matches Coq-extracted TransitionKernel per-case witnesses.")
print(f"Certificate: {certificate_path}")
PY
