#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="$ROOT/tools/aeneas"
CRATE="$ROOT/rust/magma"
OUTPUT="$ROOT/Generated"
"$ROOT/scripts/setup-tools.sh"
"$ROOT/scripts/prepare-aeneas-backend.sh"
if [[ ! -x "$BIN/charon" || ! -x "$BIN/aeneas" ]]; then
  echo "Missing Aeneas release binaries in $BIN" >&2
  exit 1
fi
cd "$CRATE"
PATH="$BIN:$PATH" "$BIN/charon" cargo --preset=aeneas \
  --start-from=crate::rounds,crate::sboxes --dest-file="$CRATE/magma-core.llbc"
"$BIN/aeneas" -backend lean "$CRATE/magma-core.llbc" \
  -dest "$OUTPUT" -subdir /RustCrypto/Code \
  -split-files -namespace RustCrypto
cd "$ROOT"
lake build RustCrypto
echo "Regenerated and checked RustCrypto cipher cores + S-boxes on Lean 4.36.0-rc2"
