#!/usr/bin/env python3
"""Audit the verification view against the pinned RustCrypto source.

The generic block encryption/decryption method bodies are unchanged. KeyInit
uses an array-based interface and a fixed-length range loop in place of
unsupported hybrid-array and zip/for_each operations; reject other edits.
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

    # The original zip/for_each iterators cannot be translated by Aeneas.
    # Their fixed-size traversal is rewritten into a range over the same
    # eight four-byte chunks; reject any other modification of the method.
    header = "impl<S: Sbox> KeyInit for Gost89<S> {"
    original = method_body(upstream, header, "new")
    expected = original.replace(
        "fn new(key: &Key<Self>) -> Self {",
        "fn new(key: &[u8; 32]) -> Self {",
    ).replace(
        "key.chunks_exact(4)\n"
        "            .zip(key_u32.iter_mut())\n"
        "            .for_each(|(chunk, v)| *v = to_u32(chunk));",
        "for i in 0..8 {\n"
        "            key_u32[i] = to_u32(&key[(i * 4)..(i * 4 + 4)]);\n"
        "        }",
    )
    if expected == original or expected != method_body(verification, header, "new"):
        raise SystemExit("KeyInit::new differs from the audited iterator-to-range rewrite")
    print("KeyInit::new: fixed-size iterator-to-range rewrite verified")



if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: check-tc26-source.py REPO_ROOT")
    check(Path(sys.argv[1]).resolve())
