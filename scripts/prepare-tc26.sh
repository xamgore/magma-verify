#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ORIGINAL="$ROOT/rust/magma/src"
TARGET="$ROOT/rust/tc26/src"
PATCH="$ROOT/patches/tc26.patch"

# Start from the pinned, unmodified RustCrypto crate on every build.
mkdir -p "$TARGET"
cp "$ORIGINAL/lib.rs" "$TARGET/lib.rs"
cp "$ORIGINAL/sboxes.rs" "$TARGET/sboxes.rs"

# Only the reviewable patch changes RustCrypto's lib.rs. The S-box source
# is a byte-for-byte copy of upstream; adapter.rs is maintained separately.
git -C "$ROOT" apply --check --directory=rust/tc26 "$PATCH"
git -C "$ROOT" apply --directory=rust/tc26 "$PATCH"
cmp "$ORIGINAL/sboxes.rs" "$TARGET/sboxes.rs"

echo "Prepared Tc26 verification crate from RustCrypto plus patches/tc26.patch."
