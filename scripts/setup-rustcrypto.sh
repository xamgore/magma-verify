#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DEST="$ROOT/rust/magma"
TOOLS="$ROOT/tools"
ARCHIVE="$TOOLS/downloads/magma-0.10.0.crate"
EXPECTED="84fcdd6a71a6af65297be074d9d26cda7a2e98b86294ee0de0732b00c2063a61"
mkdir -p "$TOOLS/downloads" "$ROOT/rust"
if [[ ! -f "$ARCHIVE" ]]; then
  shopt -s nullglob
  cached=("$HOME"/.cargo/registry/cache/*/magma-0.10.0.crate)
  if (("${#cached[@]}" > 0)); then
    cp "${cached[0]}" "$ARCHIVE"
  else
    curl -fsSL --retry 3 "https://static.crates.io/crates/magma/magma-0.10.0.crate" -o "$ARCHIVE.part"
    mv "$ARCHIVE.part" "$ARCHIVE"
  fi
fi
actual="$(shasum -a 256 "$ARCHIVE" | awk '{print $1}')"
if [[ "$actual" != "$EXPECTED" ]]; then
  echo "RustCrypto magma 0.10.0 checksum mismatch: $actual" >&2
  exit 1
fi
temp="$(mktemp -d "$TOOLS/magma-unpack.XXXXXX")"
trap 'rm -rf "$temp"' EXIT
tar -xzf "$ARCHIVE" -C "$temp"
SOURCE="$temp/magma-0.10.0"
test -f "$SOURCE/src/lib.rs"
test -f "$SOURCE/src/sboxes.rs"
if [[ -e "$DEST" ]]; then
  # Never overwrite or silently accept modified upstream source.
  diff -qr -x target -x .DS_Store "$SOURCE" "$DEST" > "$temp/diff.txt" || {
    echo "Existing rust/magma differs from the pinned original package:" >&2
    cat "$temp/diff.txt" >&2
    exit 2
  }
  echo "RustCrypto magma 0.10.0 is unmodified (SHA-256 verified)"
else
  mv "$SOURCE" "$DEST"
  echo "Restored original RustCrypto magma 0.10.0 (SHA-256 verified)"
fi
