#!/usr/bin/env bash
# Resolve a Rust toolchain that can link local verification binaries.
#
# On Apple Silicon, an x86_64 Rust/opam process may fail to invoke xcrun when
# the installed CommandLineTools only provide arm64 libxcrun. CI Linux is
# unaffected.

RUST_TOOLCHAIN_HELPER_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

is_apple_silicon_host() {
  [[ "$(uname -s 2>/dev/null || true)" == "Darwin" ]] || return 1
  [[ "$(uname -m 2>/dev/null || true)" == "arm64" ]] && return 0
  [[ "$(sysctl -in hw.optional.arm64 2>/dev/null || echo 0)" == "1" ]]
}

configure_macos_arm64_linker() {
  is_apple_silicon_host || return 0

  local sdkroot
  if [[ -z "${SDKROOT:-}" ]]; then
    sdkroot="$(arch -arm64 /usr/bin/xcrun --sdk macosx --show-sdk-path 2>/dev/null || true)"
    if [[ -n "$sdkroot" ]]; then
      export SDKROOT="$sdkroot"
    fi
  fi

  export CC_aarch64_apple_darwin="${CC_aarch64_apple_darwin:-$RUST_TOOLCHAIN_HELPER_DIR/macos_arm64_cc.sh}"
  export CARGO_TARGET_AARCH64_APPLE_DARWIN_LINKER="${CARGO_TARGET_AARCH64_APPLE_DARWIN_LINKER:-$RUST_TOOLCHAIN_HELPER_DIR/macos_arm64_cc.sh}"
  if [[ -n "${SDKROOT:-}" && -z "${CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS:-}" ]]; then
    export CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS="-C link-arg=-isysroot -C link-arg=$SDKROOT"
  fi
}

configure_verification_rust_toolchain() {
  if [[ -n "${RUSTUP_TOOLCHAIN:-}" ]]; then
    configure_macos_arm64_linker
    return 0
  fi

  if [[ -n "${CARGO_TOOLCHAIN:-}" ]]; then
    export RUSTUP_TOOLCHAIN="$CARGO_TOOLCHAIN"
    configure_macos_arm64_linker
    return 0
  fi

  local system_name machine rust_host rustc_version native_toolchain apple_silicon
  system_name="$(uname -s 2>/dev/null || true)"
  machine="$(uname -m 2>/dev/null || true)"
  rustc_version="$(rustc -Vv 2>/dev/null || true)"
  rust_host="$(awk '/^host:/ {print $2; exit}' <<<"$rustc_version")"
  apple_silicon=false
  if [[ "$system_name" == "Darwin" ]]; then
    if [[ "$machine" == "arm64" || "$(sysctl -in hw.optional.arm64 2>/dev/null || echo 0)" == "1" ]]; then
      apple_silicon=true
    fi
  fi

  if [[ "$system_name" != "Darwin" || "$apple_silicon" != "true" || "$rust_host" != "x86_64-apple-darwin" ]]; then
    configure_macos_arm64_linker
    return 0
  fi

  native_toolchain="${MACOS_ARM64_RUST_TOOLCHAIN:-stable-aarch64-apple-darwin}"
  if ! command -v rustup >/dev/null 2>&1; then
    cat >&2 <<EOF
Apple Silicon host is running an x86_64 Rust toolchain, but rustup is not available
to select a native toolchain. Install rustup or set RUSTUP_TOOLCHAIN/CARGO_TOOLCHAIN
to a native aarch64-apple-darwin toolchain before running verification scripts.
EOF
    exit 1
  fi

  local installed_toolchains
  installed_toolchains="$(rustup toolchain list 2>/dev/null || true)"
  if ! awk -v wanted="$native_toolchain" '
    {
      sub(/ .*/, "", $0)
      if ($0 == wanted) {
        found = 1
      }
    }
    END {
      exit found ? 0 : 1
    }
  ' <<<"$installed_toolchains"; then
    cat >&2 <<EOF
Apple Silicon host is running Rust host '$rust_host', which can fail to link via
xcrun when CommandLineTools only provide arm64 libxcrun.

Install the native Rust toolchain and rerun:
  rustup toolchain install $native_toolchain --force-non-host

Alternatively set RUSTUP_TOOLCHAIN or CARGO_TOOLCHAIN to an installed native
aarch64-apple-darwin toolchain.
EOF
    exit 1
  fi

  export RUSTUP_TOOLCHAIN="$native_toolchain"
  configure_macos_arm64_linker
  echo "Using Rust toolchain $RUSTUP_TOOLCHAIN for local verification on Apple Silicon."
}

configure_verification_rust_toolchain
