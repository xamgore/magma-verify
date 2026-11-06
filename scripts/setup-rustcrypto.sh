#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PACKAGE="magma"
VERSION="0.10.0"
EXPECTED="84fcdd6a71a6af65297be074d9d26cda7a2e98b86294ee0de0732b00c2063a61"
DEST="$ROOT/rust/$PACKAGE"
ARCHIVE_NAME="$PACKAGE-$VERSION.crate"

sha256() {
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    sha256sum "$1" | awk '{print $1}'
  fi
}

mkdir -p "$ROOT/tools" "$ROOT/rust"
scratch="$(mktemp -d "$ROOT/tools/rustcrypto.XXXXXX")"
trap 'rm -rf "$scratch"' EXIT

shopt -s nullglob
cached=("$HOME"/.cargo/registry/cache/*/"$ARCHIVE_NAME")
if (( ${#cached[@]} > 0 )); then
  archive="${cached[0]}"
else
  archive="$scratch/$ARCHIVE_NAME"
  curl -fL --retry 3 "https://static.crates.io/crates/$PACKAGE/$ARCHIVE_NAME" -o "$archive"
fi

if [[ "$(sha256 "$archive")" != "$EXPECTED" ]]; then
  echo "Checksum mismatch for $ARCHIVE_NAME" >&2
  exit 1
fi

tar -xzf "$archive" -C "$scratch"
source_dir="$scratch/$PACKAGE-$VERSION"
if [[ ! -f "$source_dir/src/lib.rs" ]]; then
  echo "Unexpected archive layout for $ARCHIVE_NAME" >&2
  exit 1
fi

# The managed extraction is refreshed from the verified archive on each run.
rm -rf "$DEST"
mv "$source_dir" "$DEST"
echo "Prepared $PACKAGE $VERSION from a SHA-256 verified archive."
