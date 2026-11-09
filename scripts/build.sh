#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="$ROOT/tools/aeneas"
CRATE="$ROOT/rust/magma"

"$ROOT/scripts/fetch-magma.sh"
"$ROOT/scripts/patch-magma.sh"
"$ROOT/scripts/fetch-aeneas.sh"

BACKEND="$BIN/backends/lean"
PATCH="$ROOT/scripts/aeneas-backend.patch"
if git -C "$ROOT" apply --reverse --check --directory=tools/aeneas/backends/lean "$PATCH" 2>/dev/null; then
  echo "Aeneas backend patch already applied."
else
  git -C "$ROOT" apply --check --directory=tools/aeneas/backends/lean "$PATCH"
  git -C "$ROOT" apply --directory=tools/aeneas/backends/lean "$PATCH"
  # The bundled cache and manifest target the old Lean/Mathlib versions.
  rm -rf "$BACKEND/.lake"
  rm -f "$BACKEND/lake-manifest.json"
  echo "Applied Aeneas backend patch."
fi
cmp "$ROOT/lean-toolchain" "$BACKEND/lean-toolchain"

export CARGO_TARGET_DIR="$ROOT/tools/cargo-target"
cd "$CRATE"
cargo check --locked --all-features
PATH="$BIN:$PATH" "$BIN/charon" cargo --preset=aeneas --start-from=crate::adapter::verify_key_init,crate::adapter::verify_encrypt,crate::adapter::verify_decrypt --dest-file="$ROOT/tools/magma.llbc"
"$BIN/aeneas" -backend lean "$ROOT/tools/magma.llbc" -dest "$ROOT" -subdir /Magma/Rust -namespace Magma.Rust -split-files

cd "$ROOT"
lake build
lake lint
lake exe axiom-audit --root Magma --modules-from Magma
echo "Verified Tc26 block encryption and decryption against RFC 8891."
echo "Scope: upstream cipher adapter equivalence is not proved."
