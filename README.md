# Magma verification

Formal verification workspace for the [magma](https://crates.io/crates/magma) crate from RustCrypto ecosystem.

This project uses [Lean 4](https://lean-lang.org) to prove the crate's functional correctness. The verification is done against the executable [RFC 8891](https://www.rfc-editor.org/info/rfc8891/) specification from [xamgore/magma](https://github.com/xamgore/magma) repository.

## Dependencies

- [Lean 4](https://lean-lang.org/) — the proof assistant used for the formal specification and correctness proofs.
- [Charon](https://github.com/AeneasVerif/charon) — extracts the LLBC intermediate representation from the Rust compiler.
- [Aeneas](https://github.com/AeneasVerif/aeneas) — translates Charon's LLBC output into pure Lean 4 functions and structures.

## What is proved

The TC26 encryption path matches RFC 8891 for every 256-bit key and 64-bit block. Lean covers the original S-box constants, all 1024 expanded entries, the substitution and round functions, all 32 rounds, key selection and byte order. The extracted encryption completes without modeled panics, including out-of-bounds accesses and checked-arithmetic overflow.

## What is open

The decryption round bodies and first eight-round loop have been verified, but not the complete `decrypt_block` function or its final byte output. The public `cipher` adapter, cryptographic strength, side channels and compiled machine code are also outside this proof.

## How it works

`scripts/fetch-magma.sh` restores the original `magma 0.10.0` source from a SHA-256-checked archive. Charon extracts the Rust program into LLBC[^llbc]; Aeneas translates the supported safe subset into pure Lean functions. The generated definitions are in `Magma/RustCrypto/Code/` and `Magma/RustCrypto/TC26/`. The proofs compare their behavior with `Magma/RFC8891.lean`.

Aeneas replaces ownership and borrowing with value passing and backward functions that propagate updates. Its [functional translation](https://arxiv.org/abs/2206.07185) is justified by a *simulation relation*: executions of the source semantics correspond to executions of the pure model, preserving observable results. A [soundness result for LLBC](https://arxiv.org/abs/2404.02680) also connects its borrow-aware semantics to a pointer-based execution model. This is why proofs about translated functions can establish properties of the supported Rust code. It is not a machine-checked guarantee about the actual Charon/Aeneas executables: the extraction tools and external library models remain trusted.

## Changes to the verification crate

The upstream `magma` source is unchanged. Aeneas [does not yet support `unsafe` Rust](https://github.com/AeneasVerif/aeneas#targeted-subset-and-current-limitations); the `cipher` interface uses `InOut` from the `inout` crate, which stores raw pointers and dereferences them through `unsafe`. Its `hybrid-array` types also trigger an unsupported trait cycle during translation. For this reason, `rust/tc26/` contains a separate, safe verification view with an eight-byte input/output adapter.

The original block methods are specialized from `S::g` to `TC26::g`, their `Block<Self>` argument becomes `[u8; 8]`, and `get_in()` is copied into an owned array to avoid a borrow-analysis failure. The round computations do not change. `scripts/check-tc26-source.py` enforces these exact differences, but does not establish equivalence with the public `cipher` API.

`encrypt_with_words` and `decrypt_with_words` are verification-only callers that construct the cipher and invoke a block method; they do not exist upstream. The current final encryption theorem uses the first as a convenient entry point, although neither wrapper is needed to prove a block method directly. There is no final proof about the decryption wrapper.

## Aeneas backend patches

`scripts/patch_aeneas_backend.py` adapts the Aeneas Lean library to Lean 4.36.0-rc2: it aligns Lean/Mathlib versions, discards incompatible build artifacts, updates `bv_decide` private-name construction and rewrites four `Set` membership lemmas for the current API. These changes affect the Lean proof infrastructure, not the Rust program or translation executables. The script rejects unexpected source layouts; final proof terms are still checked by Lean.

## Build

```sh
./scripts/build.sh
```

The build checks archive hashes and the Rust source comparison, regenerates Lean, compiles the crates, runs `lake build` and `lake lint`. The pinned Aeneas/Charon archive covers macOS arm64; other systems require `AENEAS_ARCHIVE_URL` and `AENEAS_ARCHIVE_SHA256`.

[^llbc]: **Low-Level Borrow Calculus**: the borrow-aware intermediate representation extracted by Charon and consumed by Aeneas.
