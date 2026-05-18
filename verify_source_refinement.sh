#!/usr/bin/env bash
set -euo pipefail

if ! command -v cargo >/dev/null 2>&1; then
  echo "cargo is required for source-level Rust refinement verification" >&2
  exit 127
fi

if ! cargo kani --version >/dev/null 2>&1; then
  echo "cargo-kani is required. Install with: cargo install --locked kani-verifier --version 0.67.0" >&2
  exit 127
fi

if [[ -z "${KANI_HOME:-}" ]]; then
  kani_version="$(cargo kani --version | awk '{print $2}')"
  kani_release_dir="${HOME}/.kani/kani-${kani_version}"
  if [[ ! -x "${kani_release_dir}/toolchain/bin/cargo" \
    && -x "${kani_release_dir}/kani-${kani_version}/toolchain/bin/cargo" ]]; then
    export KANI_HOME="${kani_release_dir}"
  fi
fi

cargo kani --output-format terse --default-unwind 16 "$@"
