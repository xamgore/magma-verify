#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="$ROOT/tools/aeneas"
CRATE="$ROOT/rust/magma"

"$ROOT/scripts/setup-rustcrypto.sh"
"$ROOT/scripts/setup-tools.sh"
python3 "$ROOT/scripts/patch_aeneas_backend.py" "$BIN/backends/lean" "$ROOT/lean-toolchain"

export CARGO_TARGET_DIR="$ROOT/tools/cargo-target"
cd "$CRATE"
cargo fmt --all --check
cargo test --locked

PATH="$BIN:$PATH" "$BIN/charon" cargo --preset=aeneas --dest-file="$ROOT/tools/magma-full.llbc"
pretty="$(mktemp "$ROOT/tools/charon-pretty.XXXXXX")"
trap 'rm -f "$pretty"' EXIT
"$BIN/charon" pretty-print "$ROOT/tools/magma-full.llbc" > "$pretty"
grep -q '::encrypt_block' "$pretty"
grep -q '::decrypt_block' "$pretty"

PATH="$BIN:$PATH" "$BIN/charon" cargo --preset=aeneas --start-from=crate::sboxes --dest-file="$ROOT/tools/magma-sboxes.llbc"
"$BIN/aeneas" -backend lean "$ROOT/tools/magma-sboxes.llbc" -dest "$ROOT" -subdir /Magma/RustCrypto/Code -split-files -namespace RustCrypto

cd "$ROOT"
lake build
lake lint
echo "Verified the original RustCrypto source and generated the S-box Lean model."
echo "Full encryption/decryption methods remain in tools/magma-full.llbc."
