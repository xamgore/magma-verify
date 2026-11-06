#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BACKEND="$ROOT/tools/aeneas/backends/lean"
if [[ ! -f "$BACKEND/lakefile.lean" ]]; then
  echo "Missing Aeneas Lean backend: unpack the macOS release into tools/aeneas first" >&2
  exit 1
fi
python3 - "$BACKEND" "$ROOT/lean-toolchain" <<'PY'
from pathlib import Path
import re, sys, json, shutil
backend = Path(sys.argv[1])
toolchain = Path(sys.argv[2]).read_text().strip()
version = toolchain.split(':v', 1)[1]
file = backend / 'lakefile.lean'
content = file.read_text()
new, count = re.subn(
    r'("https://github.com/leanprover-community/mathlib4.git"\s*@\s*)"[^"]+"',
    lambda m: m.group(1) + '"v' + version + '"', content)
if count != 1:
    raise SystemExit("Cannot find Mathlib pin in Aeneas backend")
new = new.replace('preferReleaseBuild := true', 'preferReleaseBuild := false')
manifest = backend / 'lake-manifest.json'
stale = (backend / 'lean-toolchain').read_text().strip() != toolchain
if manifest.exists():
    deps = json.loads(manifest.read_text())['packages']
    stale |= any(x.get('name') == 'mathlib' and x.get('inputRev') != 'v' + version for x in deps)
if stale:
    # The release contains prebuilt 4.35 artifacts: discard, do not reuse.
    bundled_build = backend / '.lake'
    if bundled_build.exists():
        shutil.rmtree(bundled_build)
    if manifest.exists():
        manifest.unlink()
if new != content:
    file.write_text(new)
(backend / 'lean-toolchain').write_text(toolchain + '\n')
# Lean 4.36 made enumToBitVecSuffix private and changed the reserved
# constants to private realized names. Apply the same naming as Lean 4.36.
enum_file = backend / 'AeneasMeta/BvEnumToBitVec.lean'
enum_code = enum_file.read_text()
old = '''  for suffix in [enumToBitVecSuffix, "enumToBitVec_le", "eq_iff_enumToBitVec_eq"] do
    executeReservedNameAction (.str declName suffix)'''
new = '''  let env ← getEnv
  for suffix in ["enumToBitVec", "enumToBitVec_le", "eq_iff_enumToBitVec_eq"] do
    executeReservedNameAction (mkPrivateName env (.str declName suffix))'''
if old in enum_code:
    enum_file.write_text(enum_code.replace(old, new))
elif new not in enum_code:
    raise SystemExit("Unknown Aeneas BvEnumToBitVec API; review the release")
# Lean 4.36 does not coerce Set to a predicate function in these lemmas.
lemmas_file = backend / 'Aeneas/Tactic/Solver/ScalarTac/Lemmas.lean'
lemmas_code = lemmas_file.read_text()
replacements = [
    ('''@[scalar_tac_simps] theorem Set.mem_insert_nat s x y :
  @insert ℕ (Set ℕ) Set.instInsert x s y ↔ y = x ∨ s y := by rfl''',
     '''@[scalar_tac_simps] theorem Set.mem_insert_nat (s : Set ℕ) (x y : ℕ) :
  y ∈ insert x s ↔ y = x ∨ y ∈ s := by simp'''),
    ('''@[scalar_tac_simps] theorem Set.mem_singleton_nat x y :
  @singleton ℕ (Set ℕ) Set.instSingletonSet x y ↔ y = x := by rfl''',
     '''@[scalar_tac_simps] theorem Set.mem_singleton_nat (x y : ℕ) :
  y ∈ ({x} : Set ℕ) ↔ y = x := by simp'''),
    ('''@[scalar_tac_simps] theorem Set.mem_insert_int s x y :
  @insert ℤ (Set ℤ) Set.instInsert x s y ↔ y = x ∨ s y := by rfl''',
     '''@[scalar_tac_simps] theorem Set.mem_insert_int (s : Set ℤ) (x y : ℤ) :
  y ∈ insert x s ↔ y = x ∨ y ∈ s := by simp'''),
    ('''@[scalar_tac_simps] theorem Set.mem_singleton_int x y :
  @singleton ℤ (Set ℤ) Set.instSingletonSet x y ↔ y = x := by rfl''',
     '''@[scalar_tac_simps] theorem Set.mem_singleton_int (x y : ℤ) :
  y ∈ ({x} : Set ℤ) ↔ y = x := by simp'''),
]
for before, after in replacements:
    if before in lemmas_code:
        lemmas_code = lemmas_code.replace(before, after)
    elif after not in lemmas_code:
        raise SystemExit("Unknown Aeneas Set lemma API; review release")
if lemmas_code != lemmas_file.read_text():
    lemmas_file.write_text(lemmas_code)
print("Aeneas Lean backend configured for", toolchain)
PY
