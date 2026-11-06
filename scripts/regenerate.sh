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
# Cargo snapshot has a missing bench file, so check sources with rustfmt directly.
rustfmt --edition 2024 --check src/lib.rs src/sboxes.rs src/rounds.rs
# Exercise both the extracted core and the production cipher API.
cargo test --locked
PATH="$BIN:$PATH" "$BIN/charon" cargo --preset=aeneas \
  --start-from=crate::rounds,crate::sboxes --dest-file="$CRATE/magma-core.llbc"
"$BIN/aeneas" -backend lean "$CRATE/magma-core.llbc" \
  -dest "$OUTPUT" -subdir /RustCrypto/Code \
  -split-files -namespace RustCrypto
cd "$ROOT"
# Check the generated model, the RFC spec, and the shared bridge.
lake build
# Generated/** is excluded from formatting; manually edited Lean is not.
lake lint
echo "Regenerated and checked RFC 8891 + RustCrypto core under Lean 4.36.0-rc2"
