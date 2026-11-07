#!/usr/bin/env python3
"""Reject hidden axioms in the unconditional Tc26 equivalence proof.

Lean's bv_decide tactic can introduce native SAT-checker axioms even when
all tactics complete successfully. Run #print axioms on the final theorems
and require only Lean's conventional logical axioms.
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]
names = [
    "Magma.RustCrypto.tc26_model_matches_rfc",
    "Magma.RustCrypto.tc26_apply_sbox_correct",
    "Magma.RustCrypto.tc26_g_correct",
    "Magma.RustCrypto.encrypt_block_correct",
    "Magma.RustCrypto.decrypt_block_correct",
]
audit_file = root / "tools" / "tc26-axiom-audit.lean"
audit_file.parent.mkdir(parents=True, exist_ok=True)
audit_file.write_text(
    "import Magma.RustCrypto.DecryptBlock\n"
    + "".join(f"#print axioms {name}\n" for name in names)
)
result = subprocess.run(
    ["lake", "env", "lean", str(audit_file)],
    cwd=root,
    capture_output=True,
    text=True,
)
if result.returncode:
    sys.exit(result.stdout + result.stderr)

matches = re.findall(
    r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout, re.S
)
axioms = {name: {a.strip() for a in a_list.split(",") if a.strip()}
          for name, a_list in matches}
allow = {"propext", "Classical.choice", "Quot.sound"}
if set(axioms) != set(names):
    sys.exit(f"Missing/unknown theorem in axiom audit: {result.stdout!r}")
for name in names:
    unexpected = axioms[name] - allow
    if unexpected:
        sys.exit(f"Untrusted axioms in {name}: {sorted(unexpected)}")
print("Axiom audit passed: five Tc26 theorems use only propext, Classical.choice, Quot.sound.")
