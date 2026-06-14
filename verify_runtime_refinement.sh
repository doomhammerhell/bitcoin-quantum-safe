#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR="${RUNTIME_REFINEMENT_OUT_DIR:-$ROOT_DIR/target/runtime-refinement}"
if [[ "$OUT_DIR" != /* ]]; then
  OUT_DIR="$ROOT_DIR/$OUT_DIR"
fi

cd "$ROOT_DIR"
mkdir -p "$OUT_DIR"

RUNTIME_REFINEMENT="$OUT_DIR/runtime_refinement.release.json"
CERTIFICATE="$OUT_DIR/runtime_refinement_certificate.json"

echo "Building release runtime refinement executable..."
cargo build --release --example generate_runtime_refinement

"$ROOT_DIR/target/release/examples/generate_runtime_refinement" > "$RUNTIME_REFINEMENT"

python3 - "$RUNTIME_REFINEMENT" "$CERTIFICATE" "$ROOT_DIR" <<'PY'
import hashlib
import json
import platform
import subprocess
import sys
from pathlib import Path

runtime_refinement_path, certificate_path, root_dir = sys.argv[1:]
root = Path(root_dir)


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


runtime_value = load_json(runtime_refinement_path)

if runtime_value.get("status") != "match":
    print("=== RUNTIME REFINEMENT FAILED ===")
    print(runtime_value)
    sys.exit(1)

if runtime_value.get("model") != "runtime-txid-utxo-map-refinement":
    print("=== RUNTIME REFINEMENT MODEL MISMATCH ===")
    print(runtime_value)
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
    "examples/generate_runtime_refinement.rs",
    "verify_runtime_refinement.sh",
]

release_binary = "target/release/examples/generate_runtime_refinement"
generated_output = Path(runtime_refinement_path).relative_to(root)

certificate = {
    "validation": "Runtime txid and UTXO-map refinement validation",
    "scope": {
        "claim": "release binary validates txid preimage/compute_txid wiring and runtime UTXO HashMap extensional behavior against independent deterministic references over the configured matrix",
        "non_claim": "this is not a proof of SHA-256 collision resistance, SHA-256 implementation correctness, HashMap internals, rustc, LLVM, linker, CPU, or OS correctness",
    },
    "runtime_summary": runtime_value,
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
print("Compiled runtime refinement binary validated txid and UTXO-map behavior.")
print(f"Certificate: {certificate_path}")
PY
