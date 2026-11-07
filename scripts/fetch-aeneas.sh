#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
INSTALL_DIR="$ROOT/tools/aeneas"
RELEASE="nightly-2026.11.06-4acbb6d"
RELEASES_URL="https://github.com/AeneasVerif/aeneas/releases"
RELEASE_BASE="$RELEASES_URL/download/$RELEASE"

if [[ -x "$INSTALL_DIR/aeneas" && -x "$INSTALL_DIR/charon" &&
      -f "$INSTALL_DIR/backends/lean/lakefile.lean" ]]; then
  echo "Aeneas and Charon already installed."
  exit 0
fi

platform="$(uname -s)-$(uname -m)"
if [[ -n "${AENEAS_ARCHIVE_URL:-}" || -n "${AENEAS_ARCHIVE_SHA256:-}" ]]; then
  if [[ -z "${AENEAS_ARCHIVE_URL:-}" || -z "${AENEAS_ARCHIVE_SHA256:-}" ]]; then
    echo "AENEAS_ARCHIVE_URL and AENEAS_ARCHIVE_SHA256 must be set together." >&2
    exit 1
  fi
  url="$AENEAS_ARCHIVE_URL"
  expected="$AENEAS_ARCHIVE_SHA256"
else
  case "$platform" in
    Darwin-arm64)
      archive_name="aeneas-macos-aarch64.tar.gz"
      expected="4e8ed96cf4f02478d1645c04d7f74ed1124913da588029a5743e85de8500e75c"
      ;;
    Linux-aarch64)
      archive_name="aeneas-linux-aarch64.tar.gz"
      expected="870cbcdf836cdb8734ff19ddc6343fec4a1a01801d2c33b1511c6e97ca0c1ac4"
      ;;
    Linux-x86_64)
      archive_name="aeneas-linux-x86_64.tar.gz"
      expected="257b8503464e74f17dc2dc9506b8a7440f257b4d307ad240ff3e28ec587c36b6"
      ;;
    *)
      cat >&2 <<EOF
No Aeneas binary has been configured for $platform.
Select the appropriate archive at $RELEASES_URL and run:
  AENEAS_ARCHIVE_URL=<download-url> AENEAS_ARCHIVE_SHA256=<sha256> ./scripts/build.sh
EOF
      exit 1
      ;;
  esac
  url="$RELEASE_BASE/$archive_name"
fi

sha256() {
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    sha256sum "$1" | awk '{print $1}'
  fi
}

mkdir -p "$ROOT/tools"
scratch="$(mktemp -d "$ROOT/tools/aeneas-install.XXXXXX")"
trap 'rm -rf "$scratch"' EXIT
archive="$scratch/aeneas.tar.gz"
mkdir -p "$scratch/extract"
curl -fL --retry 3 "$url" -o "$archive"

if [[ "$(sha256 "$archive")" != "$expected" ]]; then
  echo "Aeneas archive checksum mismatch." >&2
  exit 1
fi

tar -xzf "$archive" -C "$scratch/extract"
if [[ ! -x "$scratch/extract/aeneas" || ! -x "$scratch/extract/charon" ||
      ! -f "$scratch/extract/backends/lean/lakefile.lean" ]]; then
  echo "Downloaded archive does not contain the expected Aeneas/Charon layout." >&2
  exit 1
fi
rm -rf "$INSTALL_DIR"
mv "$scratch/extract" "$INSTALL_DIR"
echo "Installed Aeneas and Charon for $platform."
