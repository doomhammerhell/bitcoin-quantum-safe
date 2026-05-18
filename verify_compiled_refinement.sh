#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR="${COMPILED_REFINEMENT_OUT_DIR:-$ROOT_DIR/target/compiled-refinement}"
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

COQ_VECTORS="$(require_file "formal/coq/extraction/coq_vectors.json" "coq_vectors.json" "Coq golden vectors")"
COQ_VARINT="$(require_file "formal/coq/extraction/coq_varint_refinement.json" "coq_varint_refinement.json" "Coq varint refinement summary")"
COQ_WITNESS="$(require_file "formal/coq/extraction/coq_witness_refinement.json" "coq_witness_refinement.json" "Coq witness refinement summary")"

echo "Building release refinement executables..."
cargo build --release \
  --example generate_golden_vectors \
  --example generate_varint_refinement \
  --example generate_witness_refinement

RELEASE_EXAMPLES="$ROOT_DIR/target/release/examples"
RUST_VECTORS="$OUT_DIR/rust_vectors.release.json"
RUST_VARINT="$OUT_DIR/rust_varint_refinement.release.json"
RUST_WITNESS="$OUT_DIR/rust_witness_refinement.release.json"
CERTIFICATE="$OUT_DIR/compiled_refinement_certificate.json"

"$RELEASE_EXAMPLES/generate_golden_vectors" > "$RUST_VECTORS"
"$RELEASE_EXAMPLES/generate_varint_refinement" > "$RUST_VARINT"
"$RELEASE_EXAMPLES/generate_witness_refinement" > "$RUST_WITNESS"

python3 - "$COQ_VECTORS" "$COQ_VARINT" "$COQ_WITNESS" "$RUST_VECTORS" "$RUST_VARINT" "$RUST_WITNESS" "$CERTIFICATE" "$ROOT_DIR" <<'PY'
import hashlib
import json
import os
import platform
import subprocess
import sys
from pathlib import Path

(
    coq_vectors_path,
    coq_varint_path,
    coq_witness_path,
    rust_vectors_path,
    rust_varint_path,
    rust_witness_path,
    certificate_path,
    root_dir,
) = sys.argv[1:]

root = Path(root_dir)


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


comparisons = {
    "golden_vectors": (load_json(coq_vectors_path), load_json(rust_vectors_path)),
    "varint_refinement": (load_json(coq_varint_path), load_json(rust_varint_path)),
    "witness_refinement": (load_json(coq_witness_path), load_json(rust_witness_path)),
}

for name, (coq_value, rust_value) in comparisons.items():
    if coq_value != rust_value:
        print(f"=== COMPILED REFINEMENT MISMATCH: {name} ===")
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
    "src/encoding.rs",
    "src/kani_proofs.rs",
    "src/lib.rs",
    "src/params.rs",
    "formal/coq/VarintConcrete.v",
    "formal/coq/extraction/WitnessExtraction.v",
    "formal/coq/extraction/witness_refinement.ml",
    "formal/coq/extraction/varint_refinement.ml",
    "examples/generate_golden_vectors.rs",
    "examples/generate_varint_refinement.rs",
    "examples/generate_witness_refinement.rs",
]

release_binaries = [
    "target/release/examples/generate_golden_vectors",
    "target/release/examples/generate_varint_refinement",
    "target/release/examples/generate_witness_refinement",
]

generated_outputs = [
    Path(rust_vectors_path).relative_to(root),
    Path(rust_varint_path).relative_to(root),
    Path(rust_witness_path).relative_to(root),
]

certificate = {
    "validation": "compiled-artifact PO-8 translation validation",
    "scope": {
        "claim": "release binaries produce the same refinement summaries as the Coq-extracted artifacts over the modeled PO-8 domains",
        "non_claim": "this is not a proof of rustc, LLVM, linker, CPU, or OS correctness",
    },
    "toolchain": {
        "rustc": command_output("rustc", "-Vv"),
        "cargo": command_output("cargo", "-Vv"),
        "host": platform.platform(),
    },
    "inputs": {path: sha256(root / path) for path in tracked_inputs if (root / path).exists()},
    "release_binaries": {path: sha256(root / path) for path in release_binaries},
    "generated_outputs": {str(path): sha256(root / path) for path in generated_outputs},
    "comparisons": {name: "match" for name in comparisons},
}

with open(certificate_path, "w", encoding="utf-8") as handle:
    json.dump(certificate, handle, indent=2, sort_keys=True)
    handle.write("\n")

print("=== SUCCESS ===")
print("Compiled release binaries match Coq-extracted PO-8 refinement artifacts.")
print(f"Certificate: {certificate_path}")
PY
