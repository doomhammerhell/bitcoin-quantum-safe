#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR="${TXID_REFINEMENT_OUT_DIR:-$ROOT_DIR/target/txid-refinement}"
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

COQ_TXID="$(require_file "formal/coq/extraction/coq_txid_refinement.json" "coq_txid_refinement.json" "Coq txid refinement summary")"
RUST_TXID="$OUT_DIR/rust_txid_refinement.release.json"
CERTIFICATE="$OUT_DIR/txid_refinement_certificate.json"

echo "Building release txid refinement executable..."
cargo build --release --example generate_txid_refinement

"$ROOT_DIR/target/release/examples/generate_txid_refinement" > "$RUST_TXID"

python3 - "$COQ_TXID" "$RUST_TXID" "$CERTIFICATE" "$ROOT_DIR" <<'PY'
import hashlib
import json
import platform
import subprocess
import sys
from pathlib import Path

coq_txid_path, rust_txid_path, certificate_path, root_dir = sys.argv[1:]
root = Path(root_dir)


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


coq_value = load_json(coq_txid_path)
rust_value = load_json(rust_txid_path)

if coq_value != rust_value:
    print("=== TXID PREIMAGE REFINEMENT MISMATCH ===")
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
    "formal/coq/TxidPreimage.v",
    "formal/coq/extraction/TxidExtraction.v",
    "formal/coq/extraction/ExtractTxidVectors.v",
    "formal/coq/extraction/txid_refinement.ml",
    "examples/generate_txid_refinement.rs",
]

release_binary = "target/release/examples/generate_txid_refinement"
generated_output = Path(rust_txid_path).relative_to(root)

certificate = {
    "validation": "PO-5 txid preimage refinement validation",
    "scope": {
        "claim": "release binary produces the same txid preimage refinement summary as the Coq-extracted structural txid transcript model over the deterministic matrix",
        "non_claim": "this is not a proof of SHA-256 collision resistance, SHA-256 implementation correctness, rustc, LLVM, linker, CPU, or OS correctness",
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
print("Compiled txid refinement binary matches Coq-extracted txid preimage artifact.")
print(f"Certificate: {certificate_path}")
PY
