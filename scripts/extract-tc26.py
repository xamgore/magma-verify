#!/usr/bin/env python3
"""Prepare the Tc26 verification slice from unmodified RustCrypto Magma.

The actual encrypt_block and decrypt_block implementations are copied from
RustCrypto source, then specialized for Tc26 and mechanically unrolled.
Only the cipher-facing Block/InOut types are replaced with a minimal adapter.
The adapter's correspondence with cipher is a separate proof obligation.
"""

from pathlib import Path
import shutil
import sys


def extract_item(source: str, prefix: str) -> str:
    """Extract one brace-delimited Rust item, checking its unique start."""
    if source.count(prefix) != 1:
        raise ValueError(f"Unexpected occurrences of source item: {prefix}")
    start = source.index(prefix)
    opening = source.index("{", start)
    nesting = 0
    for index in range(opening, len(source)):
        if source[index] == "{":
            nesting += 1
        elif source[index] == "}":
            nesting -= 1
            if nesting == 0:
                return source[start : index + 1]
    raise ValueError(f"Unterminated source item: {prefix}")


def replace_once(text: str, before: str, after: str) -> str:
    if text.count(before) != 1:
        raise ValueError(f"Expected exactly one match, found {text.count(before)}: {before}")
    return text.replace(before, after, 1)


def specialize_and_unroll(body: str, encryption: bool) -> str:
    trait = "BlockCipherEncBackend" if encryption else "BlockCipherDecBackend"
    body = replace_once(
        body,
        f"impl<S: Sbox> {trait} for Gost89<S> {{",
        f"impl {trait} for Gost89<sboxes::Tc26> {{",
    )
    body = body.replace("S::g(v.1, self.key[i])", "sboxes::Tc26::g(v.1, self.key[i])")

    step = "v = (v.1, v.0 ^ sboxes::Tc26::g(v.1, self.key[i]));"
    forward = f"""for i in 0..8 {{
                {step}
            }}"""
    backward = f"""for i in (0..8).rev() {{
            {step}
        }}"""

    if encryption:
        source_schedule = f"""for _ in 0..3 {{
            {forward}
        }}
        {backward}"""
        indices = list(range(8)) * 3 + list(range(7, -1, -1))
    else:
        source_schedule = f"""for i in 0..8 {{
            {step}
        }}

        for _ in 0..3 {{
            for i in (0..8).rev() {{
                {step}
            }}
        }}"""
        indices = list(range(8)) + list(range(7, -1, -1)) * 3

    if len(indices) != 32:
        raise AssertionError("Invalid Magma key schedule")
    expanded = "\n".join(
        f"        v = (v.1, v.0 ^ sboxes::Tc26::g(v.1, self.key[{i}]));"
        for i in indices
    )
    transformed = replace_once(body, source_schedule, expanded)
    if "for i in" in transformed or "for _ in" in transformed:
        raise AssertionError("Unexpected loop after mechanical unrolling")
    if transformed.count("sboxes::Tc26::g(v.1") != 32:
        raise AssertionError("Unexpected number of original round expressions")
    return transformed


ADAPTER = """#![allow(dead_code)]
use core::{marker::PhantomData, ops::{Deref, DerefMut}};
mod sboxes;
pub use sboxes::Sbox;
use sboxes::SboxExt;

// Verification-only adapter. NOT the implementation of cipher::InOut.
pub struct Block<T> { bytes: [u8; 8], marker: PhantomData<T> }
impl<T> Block<T> {
    pub fn new(bytes: [u8; 8]) -> Self { Self { bytes, marker: PhantomData } }
}
impl<T> Deref for Block<T> {
    type Target = [u8; 8];
    fn deref(&self) -> &Self::Target { &self.bytes }
}
impl<T> DerefMut for Block<T> {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.bytes }
}
pub struct InOut<'a, 'b, T> { input: &'a T, output: &'b mut T }
impl<'a, 'b, T> InOut<'a, 'b, T> {
    pub fn get_in(&self) -> &T { self.input }
    pub fn get_out(&mut self) -> &mut T { self.output }
}
pub trait BlockCipherEncBackend: Sized {
    fn encrypt_block(&self, block: InOut<'_, '_, Block<Self>>);
}
pub trait BlockCipherDecBackend: Sized {
    fn decrypt_block(&self, block: InOut<'_, '_, Block<Self>>);
}
pub struct Gost89<S: Sbox> { key: [u32; 8], _p: PhantomData<S> }
"""

WRAPPERS = """
pub fn encrypt_with_words(key: [u32; 8], plain: [u8; 8]) -> [u8; 8] {
    let cipher = Gost89::<sboxes::Tc26> { key, _p: PhantomData };
    let input = Block::new(plain);
    let mut output = Block::new([0; 8]);
    cipher.encrypt_block(InOut { input: &input, output: &mut output });
    output.bytes
}
pub fn decrypt_with_words(key: [u32; 8], encrypted: [u8; 8]) -> [u8; 8] {
    let cipher = Gost89::<sboxes::Tc26> { key, _p: PhantomData };
    let input = Block::new(encrypted);
    let mut output = Block::new([0; 8]);
    cipher.decrypt_block(InOut { input: &input, output: &mut output });
    output.bytes
}

#[cfg(test)]
mod tests {
    use super::{encrypt_with_words, decrypt_with_words};
    use magma::cipher::{Array, BlockCipherEncrypt, BlockCipherDecrypt, KeyInit};
    use magma::Magma;

    #[test]
    fn compare_upstream_for_256_cases() {
        for seed in 0u32..256 {
            let words: [u32; 8] = core::array::from_fn(|i| {
                seed.wrapping_mul(0x9e37_79b9)
                    .rotate_left((i * 3) as u32)
                    ^ (i as u32).wrapping_mul(0xdead_beef)
            });
            let key: [u8; 32] =
                core::array::from_fn(|i| words[i / 4].to_be_bytes()[i % 4]);
            let plain = (seed as u64)
                .wrapping_mul(0x0102_0304_0506_0709)
                .to_be_bytes();
            let upstream = Magma::new(&key.into());
            let mut block = Array::try_from(plain.as_slice()).unwrap();
            upstream.encrypt_block(&mut block);
            let ciphertext: [u8; 8] = core::array::from_fn(|i| block[i]);
            assert_eq!(encrypt_with_words(words, plain), ciphertext);
            assert_eq!(decrypt_with_words(words, ciphertext), plain);
            upstream.decrypt_block(&mut block);
            assert_eq!(block.as_slice(), plain.as_slice());
        }
    }

    #[test]
    fn rfc_8891_known_answer() {
        let words = [
            0xffee_ddcc, 0xbbaa_9988, 0x7766_5544, 0x3322_1100,
            0xf0f1_f2f3, 0xf4f5_f6f7, 0xf8f9_fafb, 0xfcfd_feff,
        ];
        let plain = [0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10];
        let cipher = [0x4e, 0xe9, 0x01, 0xe5, 0xc2, 0xd8, 0xca, 0x3d];
        assert_eq!(encrypt_with_words(words, plain), cipher);
        assert_eq!(decrypt_with_words(words, cipher), plain);
    }
}
"""


def main(root: Path) -> None:
    original = root / "rust/magma/src"
    destination = root / "tools/tc26-source"
    (destination / "src").mkdir(parents=True, exist_ok=True)
    upstream = (original / "lib.rs").read_text()

    encrypt = extract_item(
        upstream, "impl<S: Sbox> BlockCipherEncBackend for Gost89<S> {"
    )
    decrypt = extract_item(
        upstream, "impl<S: Sbox> BlockCipherDecBackend for Gost89<S> {"
    )
    conversion = extract_item(
        upstream, "#[inline(always)]\nfn to_u32(chunk: &[u8]) -> u32 {"
    )
    output = "\n\n".join(
        [
            ADAPTER,
            specialize_and_unroll(encrypt, encryption=True),
            specialize_and_unroll(decrypt, encryption=False),
            conversion,
            WRAPPERS,
        ]
    )
    (destination / "Cargo.toml").write_text(
        '[package]\nname = "magma_tc26_slice"\nversion = "0.0.0"\nedition = "2024"\n'
        '\n[dev-dependencies]\nmagma = { path = "../../rust/magma" }\n'
    )
    shutil.copyfile(original / "sboxes.rs", destination / "src/sboxes.rs")
    (destination / "src/lib.rs").write_text(output)
    print("Prepared original RustCrypto method bodies for Tc26; unrolled 32 rounds per method.")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: extract-tc26.py REPOSITORY_ROOT")
    main(Path(sys.argv[1]).resolve())
