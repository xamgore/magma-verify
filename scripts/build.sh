#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="$ROOT/tools/aeneas"
CRATE="$ROOT/rust/magma"

"$ROOT/scripts/fetch-magma.sh"
"$ROOT/scripts/patch-magma.sh"
"$ROOT/scripts/fetch-aeneas.sh"
python3 "$ROOT/scripts/patch_aeneas_backend.py" "$BIN/backends/lean" "$ROOT/lean-toolchain"
python3 "$ROOT/scripts/check-tc26-source.py" "$ROOT"

export CARGO_TARGET_DIR="$ROOT/tools/cargo-target"
cd "$CRATE"
cargo check --locked --all-features
PATH="$BIN:$PATH" "$BIN/charon" cargo --preset=aeneas --start-from=crate::adapter::verify_encrypt,crate::adapter::verify_decrypt --dest-file="$ROOT/tools/magma.llbc"
"$BIN/aeneas" -backend lean "$ROOT/tools/magma.llbc" -dest "$ROOT" -subdir /Magma/RustCrypto/Tc26 -namespace RustCryptoTc26 -split-files

cd "$ROOT"
lake build
lake lint
python3 "$ROOT/scripts/audit-lean-axioms.py"
echo "Verified Tc26 block encryption and decryption against RFC 8891."
echo "Scope: upstream cipher adapter equivalence is not proved."
