#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="$ROOT/tools/aeneas"
CRATE="$ROOT/rust/magma"
OUTPUT="$ROOT/Generated"
if [[ ! -x "$BIN/charon" || ! -x "$BIN/aeneas" ]]; then
  echo "Missing Aeneas release binaries: $BIN" >&2
  exit 1
fi
cd "$CRATE"
PATH="$BIN:$PATH" "$BIN/charon" cargo --preset=aeneas \
  --start-from=crate::sboxes --dest-file="$CRATE/magma-sboxes.llbc"
"$BIN/aeneas" -backend lean "$CRATE/magma-sboxes.llbc" \
  -dest "$OUTPUT" -subdir /RustCrypto/Code \
  -split-files -namespace RustCrypto
echo "Generated: $OUTPUT/RustCrypto/Code/{Types,Funs}.lean"
