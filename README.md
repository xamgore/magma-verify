# Magma verification

Formal verification workspace for the [magma](https://crates.io/crates/magma) crate from the RustCrypto ecosystem.

This project uses [Lean 4](https://lean-lang.org) to prove the crate's functional correctness. The verification is done against the executable [RFC 8891](https://www.rfc-editor.org/info/rfc8891/) specification from [xamgore/magma](https://github.com/xamgore/magma) repository.

### How it works

[Charon](https://github.com/AeneasVerif/charon) extracts Rust’s MIR into LLBC, which tracks borrows. [Aeneas](https://github.com/AeneasVerif/aeneas) translates it into pure Lean functions, representing Rust state changes as return values rather than mutations.

The basis for transferring proofs is **forward simulation** between Rust’s operational semantics and its functional model in Lean. Aeneas guarantees that every execution step of the source program is mathematically simulated by the Lean model.

Because any concrete Rust trace maps to a corresponding Lean trace, proving a property—such as functional correctness or panic freedom—for the Lean function mathematically guarantees that the source Rust code cannot diverge from this behavior. This soundness [is formally established](https://arxiv.org/abs/2404.02680) through a verified chain of simulation relations linking concrete execution to the functional model.

#### What is proved

The crate's [`encrypt_block`](https://docs.rs/magma/0.10.0/src/magma/lib.rs.html#98-115) and [`decrypt_block`](https://docs.rs/magma/0.10.0/src/magma/lib.rs.html#124-143) method bodies match RFC 8891 for every possible secret key and text input. Both methods terminate without panics from out-of-bounds access, checked arithmetic overflow or failed byte conversions. Key initialization also preserves the RFC 8891 key when converting 32 bytes into eight big-endian words.

#### What is open

The MIR/LLBC-level model omits timing and microarchitectural effects, so the proof gives no guarantees about side-channel resistance. It also cannot rule out bugs introduced by rustc or LLVM.

### Limitations

Aeneas cannot translate the `unsafe` code behind the pointer-based [`InOut`](https://docs.rs/inout/0.2.2/inout/struct.InOut.html), so we replace it with a safe I/O adapter. [`Block<Self>`](https://docs.rs/cipher/0.5.1/cipher/type.Block.html) depends on [`hybrid-array`](https://docs.rs/hybrid-array/0.4.10/hybrid_array/struct.Array.html)'s generic associated types, which Aeneas cannot handle under its default `--lift-associated-types` flag; we use `[u8; 8]` instead. We also specialize `S::g` to the specific [`Tc26`](https://docs.rs/magma/0.10.0/src/magma/sboxes.rs.html#49-55) implementation. For `KeyInit`, we replace chained iterators with an eight-iteration `for` loop.

### Aeneas backend patches

To upgrade the Aeneas Lean backend from version `4.35.0` to `4.36.0-rc2`, we apply the following patches:

- Four `Set` membership lemmas in `ScalarTac/Lemmas.lean` are restated with equivalent proofs for the updated Mathlib API.
- The Lean and Mathlib versions are pinned to 4.36.0-rc2, and incompatible prebuilt artifacts are discarded.
- In `BvEnumToBitVec.lean`, obsolete private-name construction is replaced by `mkPrivateName` to keep `bv_decide` proof generation compatible with the new Lean API.

These changes do not affect the correctness of Magma's verification.

### Build

```sh
./scripts/build.sh
```

The script fetches `magma 0.10.0` and the pinned [Aeneas/Charon](https://github.com/AeneasVerif/aeneas/releases/tag/nightly-2026.11.06-4acbb6d) release, applies Aeneas backend patches, checks the Rust specialization, extracts LLBC, generates Lean, and runs Rust compilation checks, `lake build`, `lake lint` and the axiom audit.

`fetch-aeneas.sh` selects the release archive for macOS ARM64, Linux ARM64 or Linux x86-64. Other platforms can pass `AENEAS_ARCHIVE_URL` and `AENEAS_ARCHIVE_SHA256` environment variables to the script.
