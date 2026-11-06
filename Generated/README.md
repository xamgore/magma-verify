# Generated RustCrypto model

This directory contains **Aeneas output in the root Lean 4.36 project**.
There is intentionally no nested Lake project, toolchain, or manifest.

Run from the repository root:

```sh
./scripts/regenerate.sh
lake build
```

Charon extracts `crate::rounds` and `crate::sboxes` from the local
RustCrypto Magma verification fork using `--preset=aeneas`. Aeneas
translates their LLBC into `RustCrypto/Code/Types.lean` and `Funs.lean`.
The script runs the root `lake build RustCrypto` afterwards.

Unlike an independent hand-written model, `encrypt_block_core` and
`decrypt_block_core` are called by production RustCrypto cipher adapters.

**Limitations:** the `cipher::InOut` adapters themselves have not been
translated, and recursive round schedules use Lean `partial_fixpoint`
until termination is formally established. No equivalence theorem
against `Magma/RFC8891.lean` has been proved yet.

Do not hand-format or edit generated Lean files: edit the Rust source,
then regenerate. The project's `lean-fmt.toml` excludes this directory.
