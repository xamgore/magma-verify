#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="$ROOT/tools/aeneas"
CRATE="$ROOT/rust/magma"
OUTPUT="$ROOT/Generated"
"$ROOT/scripts/setup-rustcrypto.sh"
"$ROOT/scripts/setup-tools.sh"
"$ROOT/scripts/prepare-aeneas-backend.sh"

cd "$CRATE"
cargo fmt --all --check
cargo test --locked

# Keep the original RustCrypto encryption/decryption methods in the complete
# LLBC model. Aeneas cannot yet translate the cipher/hybrid-array trait graph.
PATH="$BIN:$PATH" "$BIN/charon" cargo --preset=aeneas \
  --dest-file="$ROOT/tools/magma-full.llbc"
"$BIN/charon" pretty-print "$ROOT/tools/magma-full.llbc" \
  > "$ROOT/tools/magma-full.pretty.txt"
grep -q '::encrypt_block' "$ROOT/tools/magma-full.pretty.txt"
grep -q '::decrypt_block' "$ROOT/tools/magma-full.pretty.txt"

# Translate only real code from the original crate, without rewriting it.
PATH="$BIN:$PATH" "$BIN/charon" cargo --preset=aeneas \
  --start-from=crate::sboxes --dest-file="$ROOT/tools/magma-sboxes.llbc"
"$BIN/aeneas" -backend lean "$ROOT/tools/magma-sboxes.llbc" \
  -dest "$OUTPUT" -subdir /RustCrypto/Code -split-files -namespace RustCrypto

cd "$ROOT"
lake build
lake lint
echo "Verified unchanged RustCrypto source and generated original S-box model."
echo "Full original encrypt/decrypt methods are preserved in magma-full.llbc; Lean translation remains open."
