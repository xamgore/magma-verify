#!/usr/bin/env python3
"""Check that the Tc26 verification methods retain the original RustCrypto loops.

No Rust code is generated or modified by this script. The verification crate
uses only two deliberate source transformations:
  * S::g(...) -> sboxes::Tc26::g(...)
  * let b = block.get_in(); -> let b = block.get_in().bytes;

Both changes are outside the cipher's round schedule. If upstream changes,
the build fails until the verification source is reviewed and synchronized.
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
    for trait, name in (
        ("BlockCipherEncBackend", "encrypt_block"),
        ("BlockCipherDecBackend", "decrypt_block"),
    ):
        original = method_body(
            upstream, f"impl<S: Sbox> {trait} for Gost89<S> {{", name
        )
        actual = method_body(
            verification,
            f"impl {trait} for Gost89<sboxes::Tc26> {{",
            name,
        )
        assert original.count("let b = block.get_in();") == 1
        assert original.count("S::g(") > 0
        expected = original.replace(
            "let b = block.get_in();", "let b = block.get_in().bytes;"
        ).replace("S::g(", "sboxes::Tc26::g(")
        if actual != expected:
            differences = difflib.unified_diff(
                expected.splitlines(),
                actual.splitlines(),
                fromfile=f"original {name} after two approved substitutions",
                tofile=f"rust/tc26 {name}",
                lineterm="",
            )
            print("\n".join(differences), file=sys.stderr)
            raise SystemExit(f"{name}: verification source differs from RustCrypto")
        print(f"{name}: original loops and Feistel operations match")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: check-tc26-source.py REPO_ROOT")
    check(Path(sys.argv[1]).resolve())
