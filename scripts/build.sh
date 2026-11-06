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

# Extract the original method bodies, specialize to Tc26, and mechanically
# expand their finite loops. No modifications to the upstream crate.
python3 "$ROOT/scripts/extract-tc26.py" "$ROOT"
cargo test --manifest-path "$ROOT/tools/tc26-source/Cargo.toml"
cd "$ROOT/tools/tc26-source"
PATH="$BIN:$PATH" "$BIN/charon" cargo --preset=aeneas --start-from=crate::encrypt_with_words,crate::decrypt_with_words --dest-file="$ROOT/tools/magma-tc26.llbc"
"$BIN/aeneas" -backend lean "$ROOT/tools/magma-tc26.llbc" -dest "$ROOT" -subdir /Magma/RustCrypto/Tc26 -namespace RustCryptoTc26 -split-files

cd "$ROOT"
lake build
lake lint
echo "Built the original S-box model and the Tc26-specialized original method bodies."
echo "Note: the Tc26 adapter and mechanical loop expansion are not yet formally proved equivalent."
