#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CRATE="$ROOT/rust/magma"
PATCH="$ROOT/rust/src/tc26.patch"

# The verified archive is freshly extracted by fetch-magma.sh.

git -C "$ROOT" apply --check --directory=rust/magma "$PATCH"
git -C "$ROOT" apply --directory=rust/magma "$PATCH"
cp "$ROOT/rust/src/adapter.rs" "$CRATE/src/adapter.rs"
cp "$ROOT/rust/Cargo.lock" "$CRATE/Cargo.lock"

echo "Applied verification adapter to the pinned RustCrypto magma crate."
