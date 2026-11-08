#!/usr/bin/env python3
"""Verify that Tc26's cipher algorithm matches the published RustCrypto source.

The verification view substitutes only the block backend interface with
a safe adapter. Both original generic backend implementations, including
all cipher rounds and S-box dispatch, must be byte-for-byte unchanged.
"""

import difflib
import sys
from pathlib import Path


def method_body(source: str, impl_header: str, method: str) -> str:
    start = source.index(impl_header)
    decl = source.index(f"fn {method}(", start)
    begin = source.index("{", decl)
    level = 0
    for i in range(begin, len(source)):
        if source[i] == "{":
            level += 1
        elif source[i] == "}":
            level -= 1
            if level == 0:
                return source[decl : i + 1]
    raise ValueError(f"Unterminated method: {method}")


def check(root: Path) -> None:
    upstream = (root / "tools/magma-original-lib.rs").read_text()
    verification = (root / "rust/magma/src/lib.rs").read_text()
    for trait, method in (
        ("BlockCipherEncBackend", "encrypt_block"),
        ("BlockCipherDecBackend", "decrypt_block"),
    ):
        header = f"impl<S: Sbox> {trait} for Gost89<S> {{"
        original = method_body(upstream, header, method)
        actual = method_body(verification, header, method)
        if actual != original:
            differences = difflib.unified_diff(
                original.splitlines(),
                actual.splitlines(),
                fromfile=f"upstream {trait}::{method}",
                tofile=f"verification {trait}::{method}",
                lineterm="",
            )
            print("\n".join(differences), file=sys.stderr)
            raise SystemExit(f"{method}: verification method diverges from upstream")
        print(f"{method}: original RustCrypto method body unchanged")



if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: check-tc26-source.py REPO_ROOT")
    check(Path(sys.argv[1]).resolve())
