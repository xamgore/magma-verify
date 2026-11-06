#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TOOLS="$ROOT/tools/aeneas"
if [[ -x "$TOOLS/aeneas" && -x "$TOOLS/charon" && -f "$TOOLS/backends/lean/lakefile.lean" ]]; then
  echo "Aeneas + Charon are already installed in $TOOLS"
  exit 0
fi
if [[ "$(uname -s)" != "Darwin" || "$(uname -m)" != "arm64" ]]; then
  echo "This pinned release is for macOS ARM64 only" >&2
  exit 1
fi
URL="https://github.com/AeneasVerif/aeneas/releases/download/nightly-2026.11.06-4acbb6d/aeneas-macos-aarch64.tar.gz"
HASH="4e8ed96cf4f02478d1645c04d7f74ed1124913da588029a5743e85de8500e75c"
ARCHIVE="$ROOT/tools/downloads/aeneas-macos-aarch64.tar.gz"
mkdir -p "$TOOLS" "$(dirname "$ARCHIVE")"
if [[ ! -f "$ARCHIVE" ]]; then
  curl -fL --retry 3 "$URL" -o "$ARCHIVE.part"
  mv "$ARCHIVE.part" "$ARCHIVE"
fi
ACTUAL="$(shasum -a 256 "$ARCHIVE" | awk '{print $1}')"
if [[ "$ACTUAL" != "$HASH" ]]; then
  echo "Aeneas SHA-256 mismatch: $ACTUAL" >&2
  exit 1
fi
tar -xzf "$ARCHIVE" -C "$TOOLS"
echo "Installed pinned Aeneas + bundled Charon in $TOOLS"
