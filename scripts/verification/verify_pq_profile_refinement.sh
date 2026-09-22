#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
source "$SCRIPT_DIR/rust_toolchain.sh"
OUT_DIR="${PQ_PROFILE_REFINEMENT_OUT_DIR:-$ROOT_DIR/target/pq-profile-refinement}"
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

COQ_PQ_PROFILE="$(require_file "formal/coq/extraction/coq_pq_profile_refinement.json" "coq_pq_profile_refinement.json" "Coq PQ profile refinement summary")"
RUST_PQ_PROFILE="$OUT_DIR/rust_pq_profile_refinement.release.json"
CERTIFICATE="$OUT_DIR/pq_profile_refinement_certificate.json"

echo "Building release PQ profile refinement executable..."
cargo build --release --example generate_pq_profile_refinement

"$ROOT_DIR/target/release/examples/generate_pq_profile_refinement" > "$RUST_PQ_PROFILE"

python3 - "$COQ_PQ_PROFILE" "$RUST_PQ_PROFILE" "$CERTIFICATE" "$ROOT_DIR" <<'PY'
import hashlib
import json
import os
import platform
import subprocess
import sys
from pathlib import Path

coq_pq_profile_path, rust_pq_profile_path, certificate_path, root_dir = sys.argv[1:]
root = Path(root_dir)


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


coq_value = load_json(coq_pq_profile_path)
rust_value = load_json(rust_pq_profile_path)

if coq_value != rust_value:
    print("=== PQ PROFILE REFINEMENT MISMATCH ===")
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


def relpath(path):
    return os.path.relpath(path, root)


tracked_inputs = [
    "Cargo.lock",
    "Cargo.toml",
    "src/lib.rs",
    "src/params.rs",
    "src/encoding.rs",
    "src/pq_profile.rs",
    "formal/coq/PQProfile.v",
    "formal/coq/extraction/PQProfileExtraction.v",
    "formal/coq/extraction/ExtractPQProfileVectors.v",
    "formal/coq/extraction/pq_profile_refinement.ml",
    "examples/generate_pq_profile_refinement.rs",
    "scripts/verification/verify_pq_profile_refinement.sh",
]

release_binary = root / "target/release/examples/generate_pq_profile_refinement"
generated_output = Path(rust_pq_profile_path)

certificate = {
    "validation": "PQ signature-suite profile refinement validation",
    "scope": {
        "claim": "release binary derives the same PQ profile, witness-size, consensus-activation, and reserved-fallback summary as the Coq-extracted PQProfile artifact",
        "non_claim": "this is not a proof of FIPS 204/FIPS 205 primitive security, signature library correctness, rustc, LLVM, linker, CPU, or OS correctness",
    },
    "evidence": {
        "format": "structured-pq-profile-summary",
        "profile_count": coq_value.get("profile_count"),
        "consensus_enabled_schemes": coq_value.get("consensus_enabled_schemes"),
        "implemented_schemes": coq_value.get("implemented_schemes"),
        "properties": coq_value.get("properties"),
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
print("Compiled PQ profile refinement binary matches Coq-extracted profile boundary.")
print(f"Certificate: {certificate_path}")
PY
