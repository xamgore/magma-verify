# RustCrypto models

`Code/` contains the direct Aeneas translation of the original S-box
functions. `Tc26/` contains generated Lean for original
`encrypt_block`/`decrypt_block` bodies, mechanically specialized to
Tc26 and expanded to 32 explicit rounds.

Run `./scripts/build.sh` at the repository root to regenerate both.
Do not edit the generated Lean files.

The full original method signatures are preserved in
`tools/magma-full.llbc`. The Tc26 extraction uses a simplified
`Block`/`InOut` adapter. Rust tests compare it against the actual
RustCrypto implementation, but the adapter and loop expansion still
require formal justification.
