#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR="${TRANSITION_REFINEMENT_OUT_DIR:-$ROOT_DIR/target/transition-refinement}"
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

COQ_TRANSITION="$(require_file "formal/coq/extraction/coq_transition_refinement.json" "coq_transition_refinement.json" "Coq transition/final-state refinement summary")"
RUST_TRANSITION="$OUT_DIR/rust_transition_refinement.release.json"
CERTIFICATE="$OUT_DIR/transition_refinement_certificate.json"

echo "Building release transition refinement executable..."
cargo build --release --example generate_transition_refinement

"$ROOT_DIR/target/release/examples/generate_transition_refinement" > "$RUST_TRANSITION"

python3 - "$COQ_TRANSITION" "$RUST_TRANSITION" "$CERTIFICATE" "$ROOT_DIR" <<'PY'
import hashlib
import json
import platform
import subprocess
import sys
from pathlib import Path

coq_transition_path, rust_transition_path, certificate_path, root_dir = sys.argv[1:]
root = Path(root_dir)


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


coq_value = load_json(coq_transition_path)
rust_value = load_json(rust_transition_path)

if coq_value != rust_value:
    print("=== TRANSITION REFINEMENT MISMATCH ===")
    print(f"Coq:  {coq_value}")
    print(f"Rust: {rust_value}")
    sys.exit(1)


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
    "src/types.rs",
    "src/migration.rs",
    "src/freeze.rs",
    "src/weight.rs",
    "src/params.rs",
    "formal/coq/UTXOTransitions.v",
    "formal/coq/extraction/TransitionExtraction.v",
    "formal/coq/extraction/ExtractTransitionVectors.v",
    "formal/coq/extraction/transition_refinement.ml",
    "examples/generate_transition_refinement.rs",
]

release_binary = "target/release/examples/generate_transition_refinement"
generated_output = Path(rust_transition_path).relative_to(root)

certificate = {
    "validation": "PO-5 UTXO transition/final-state refinement validation",
    "scope": {
        "claim": "release binary observing Rust structural entrypoints produces the same accept/reject and projected-final-state transition refinement summary as the Coq-extracted structural UTXO transition model over the deterministic projection matrix",
        "non_claim": "this is not a proof of SHA-256 txid collision resistance, UTXO-store backend internals, cryptographic witness verification, rustc, LLVM, linker, CPU, or OS correctness",
    },
    "projection": {
        "coq": "association-list UTXO indexed by abstract nat outpoint IDs",
        "rust": "UtxoSet/UtxoStore UTXO indexed by synthetic OutPoint values; fresh IDs are mapped to compute_txid(tx), vout",
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
print("Compiled transition refinement binary matches Coq-extracted UTXO transition/final-state artifact.")
print(f"Certificate: {certificate_path}")
PY
