#!/usr/bin/env python3
"""Adapt the installed Aeneas Lean backend to the project's Lean toolchain."""

import json
import re
import shutil
import sys
from pathlib import Path


def replace_known(path: Path, original: str, replacement: str) -> None:
    """Apply an idempotent patch, rejecting unknown upstream source layouts."""
    content = path.read_text()
    if original in content:
        path.write_text(content.replace(original, replacement))
    elif replacement not in content:
        raise RuntimeError(f"Unexpected Aeneas source layout: {path}")


def prepare_backend(backend: Path, toolchain_file: Path) -> None:
    toolchain = toolchain_file.read_text().strip()
    version = toolchain.split(":v", 1)[1]

    lakefile = backend / "lakefile.lean"
    content = lakefile.read_text()
    updated, count = re.subn(
        r'("https://github.com/leanprover-community/mathlib4.git"\s*@\s*)"[^"]+"',
        lambda match: match.group(1) + f'"v{version}"',
        content,
    )
    if count != 1:
        raise RuntimeError("Cannot find Mathlib pin in Aeneas backend")
    updated = updated.replace("preferReleaseBuild := true", "preferReleaseBuild := false")

    manifest = backend / "lake-manifest.json"
    stale = (backend / "lean-toolchain").read_text().strip() != toolchain
    if manifest.exists():
        dependencies = json.loads(manifest.read_text()).get("packages", [])
        stale |= any(
            pkg.get("name") == "mathlib" and pkg.get("inputRev") != f"v{version}"
            for pkg in dependencies
        )

    if stale:
        # The release ships prebuilt artifacts for a different Lean version.
        shutil.rmtree(backend / ".lake", ignore_errors=True)
        manifest.unlink(missing_ok=True)

    if updated != content:
        lakefile.write_text(updated)
    (backend / "lean-toolchain").write_text(toolchain + "\n")

    replace_known(
        backend / "AeneasMeta/BvEnumToBitVec.lean",
        """  for suffix in [enumToBitVecSuffix, "enumToBitVec_le", "eq_iff_enumToBitVec_eq"] do
    executeReservedNameAction (.str declName suffix)""",
        """  let env ← getEnv
  for suffix in ["enumToBitVec", "enumToBitVec_le", "eq_iff_enumToBitVec_eq"] do
    executeReservedNameAction (mkPrivateName env (.str declName suffix))""",
    )

    set_lemmas = backend / "Aeneas/Tactic/Solver/ScalarTac/Lemmas.lean"
    replacements = [
        (
            """@[scalar_tac_simps] theorem Set.mem_insert_nat s x y :
  @insert ℕ (Set ℕ) Set.instInsert x s y ↔ y = x ∨ s y := by rfl""",
            """@[scalar_tac_simps] theorem Set.mem_insert_nat (s : Set ℕ) (x y : ℕ) :
  y ∈ insert x s ↔ y = x ∨ y ∈ s := by simp""",
        ),
        (
            """@[scalar_tac_simps] theorem Set.mem_singleton_nat x y :
  @singleton ℕ (Set ℕ) Set.instSingletonSet x y ↔ y = x := by rfl""",
            """@[scalar_tac_simps] theorem Set.mem_singleton_nat (x y : ℕ) :
  y ∈ ({x} : Set ℕ) ↔ y = x := by simp""",
        ),
        (
            """@[scalar_tac_simps] theorem Set.mem_insert_int s x y :
  @insert ℤ (Set ℤ) Set.instInsert x s y ↔ y = x ∨ s y := by rfl""",
            """@[scalar_tac_simps] theorem Set.mem_insert_int (s : Set ℤ) (x y : ℤ) :
  y ∈ insert x s ↔ y = x ∨ y ∈ s := by simp""",
        ),
        (
            """@[scalar_tac_simps] theorem Set.mem_singleton_int x y :
  @singleton ℤ (Set ℤ) Set.instSingletonSet x y ↔ y = x := by rfl""",
            """@[scalar_tac_simps] theorem Set.mem_singleton_int (x y : ℤ) :
  y ∈ ({x} : Set ℤ) ↔ y = x := by simp""",
        ),
    ]
    for original, replacement in replacements:
        replace_known(set_lemmas, original, replacement)

    print(f"Aeneas Lean backend prepared for {toolchain}")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("Usage: patch_aeneas_backend.py BACKEND_DIR LEAN_TOOLCHAIN")
    prepare_backend(Path(sys.argv[1]), Path(sys.argv[2]))
