# Tc26 verification crate

Open `Cargo.toml` in your Rust IDE. `src/lib.rs` is the exact code passed
to Charon and Aeneas. It contains the original RustCrypto encryption and
decryption loops, specialized to `Tc26`. S-box definitions are compiled
directly from `../magma/src/sboxes.rs`.

The only local `cipher` replacement is `src/adapter.rs`: a small
`InOut` structure with `get_in` and `get_out` for eight-byte arrays.
There are **no reproduced BlockCipher traits or Block structs**.

Within the original RustCrypto method bodies the only changes are:
- `S::g` → `sboxes::Tc26::g`.
- `InOut<'_, '_, Block<Self>>` → `InOut<'_, '_, [u8; 8]>`.
- `let b = block.get_in();` → `let b = *block.get_in();`.

These changes are checked by `scripts/check-tc26-source.py`. All original
loops, their bounds, and the Feistel expressions remain unchanged.

```sh
../../scripts/setup-rustcrypto.sh
cargo check --locked
cargo test --locked
cargo fmt --all --check
```

Tests compare with the original `magma::Magma` on 256 deterministic
key/block pairs and verify a known RFC vector. The I/O adapter's
equivalence to the real `cipher` API has not yet been formally proved.
