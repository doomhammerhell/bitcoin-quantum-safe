#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR="${SIGHASH_REFINEMENT_OUT_DIR:-$ROOT_DIR/target/sighash-refinement}"
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

COQ_SIGHASH="$(require_file "formal/coq/extraction/coq_sighash_refinement.json" "coq_sighash_refinement.json" "Coq sighash refinement summary")"
RUST_SIGHASH="$OUT_DIR/rust_sighash_refinement.release.json"
CERTIFICATE="$OUT_DIR/sighash_refinement_certificate.json"

echo "Building release sighash refinement executable..."
cargo build --release --example generate_sighash_refinement

"$ROOT_DIR/target/release/examples/generate_sighash_refinement" > "$RUST_SIGHASH"

python3 - "$COQ_SIGHASH" "$RUST_SIGHASH" "$CERTIFICATE" "$ROOT_DIR" <<'PY'
import hashlib
import json
import platform
import subprocess
import sys
from pathlib import Path

coq_sighash_path, rust_sighash_path, certificate_path, root_dir = sys.argv[1:]
root = Path(root_dir)


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


coq_value = load_json(coq_sighash_path)
rust_value = load_json(rust_sighash_path)

if coq_value != rust_value:
    print("=== SIGHASH TRANSCRIPT REFINEMENT MISMATCH ===")
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
    "src/sighash.rs",
    "src/types.rs",
    "formal/coq/SighashV2.v",
    "formal/coq/extraction/SighashExtraction.v",
    "formal/coq/extraction/ExtractSighashVectors.v",
    "formal/coq/extraction/sighash_refinement.ml",
    "examples/generate_sighash_refinement.rs",
]

release_binary = "target/release/examples/generate_sighash_refinement"
generated_output = Path(rust_sighash_path).relative_to(root)

certificate = {
    "validation": "PO-4 sighash transcript refinement validation",
    "scope": {
        "claim": "release binary produces the same sighash transcript refinement summary as the Coq-extracted structural serializer over the modeled matrix",
        "non_claim": "this is not a proof of SHA-256, rustc, LLVM, linker, CPU, or OS correctness",
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
print("Compiled sighash refinement binary matches Coq-extracted transcript artifact.")
print(f"Certificate: {certificate_path}")
PY
