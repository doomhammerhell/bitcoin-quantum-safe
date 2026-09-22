#!/usr/bin/env bash
set -euo pipefail

exec arch -arm64 /usr/bin/cc "$@"
