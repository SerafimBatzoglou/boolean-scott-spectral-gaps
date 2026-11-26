#!/usr/bin/env bash
# Run from a checkout with the Lean toolchain and Lake dependencies available.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean --version
lake build
lake env lean Audit.lean

# Each module is replayed in a fresh process.
lake env bash -euo pipefail -c '
  count=0
  for file in BooleanScott/*.lean; do
    name=${file#BooleanScott/}
    module=BooleanScott.${name%.lean}
    leanchecker "$module"
    printf "Kernel replay passed: %s\n" "$module"
    count=$((count + 1))
  done
  printf "Kernel replay passed: %s proof modules.\n" "$count"
'
