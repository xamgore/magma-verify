#!/usr/bin/env python3
"""Verify that Tc26's cipher algorithm matches the published RustCrypto source.

The verification model replaces the generic trait interface with an inherent
Tc26 method over eight-byte arrays, and copies the eight input bytes before
running the original loops. Apart from S -> Tc26 and that input adaptation,
the algorithm's Rust method bodies must match exactly.
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
    upstream = (root / "rust/magma/src/lib.rs").read_text()
    verification = (root / "rust/tc26/src/lib.rs").read_text()
    specialization = "impl Gost89<sboxes::Tc26> {"
    if verification.count(specialization) != 2:
        raise SystemExit("Expected two inherent Tc26 method implementations")

    for trait, method in (
        ("BlockCipherEncBackend", "encrypt_block"),
        ("BlockCipherDecBackend", "decrypt_block"),
    ):
        original = method_body(
            upstream, f"impl<S: Sbox> {trait} for Gost89<S> {{", method
        )
        actual = method_body(verification, specialization, method)
        original_signature = (
            f"fn {method}(&self, mut block: InOut<'_, '_, Block<Self>>)"
        )
        adapted_signature = (
            f"fn {method}(&self, mut block: InOut<'_, '_, [u8; 8]>)"
        )
        if original.count(original_signature) != 1:
            raise SystemExit(f"Unexpected upstream signature for {method}")
        if original.count("let b = block.get_in();") != 1:
            raise SystemExit(f"Unexpected upstream input read for {method}")
        if original.count("S::g(") == 0:
            raise SystemExit(f"Missing upstream Feistel rounds in {method}")

        expected = (
            original.replace(original_signature, adapted_signature)
            .replace("let b = block.get_in();", "let b = *block.get_in();")
            .replace("S::g(", "sboxes::Tc26::g(")
        )
        if actual != expected:
            differences = difflib.unified_diff(
                expected.splitlines(),
                actual.splitlines(),
                fromfile=f"upstream {method} after approved interface substitutions",
                tofile=f"tc26::{method}",
                lineterm="",
            )
            print("\n".join(differences), file=sys.stderr)
            raise SystemExit(f"{method}: verification method diverges from upstream")
        print(f"{method}: original loops, indices and Feistel expressions match")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: check-tc26-source.py REPO_ROOT")
    check(Path(sys.argv[1]).resolve())
