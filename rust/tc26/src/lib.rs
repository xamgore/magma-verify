//! Tc26-specific verification view of RustCrypto Magma 0.10.0.
//!
//! Upstream source: rust/magma/src/lib.rs, rust/magma/src/sboxes.rs.
//! This crate is CHECKED IN so rust-analyzer, rustfmt, Cargo and reviewers can
//! inspect the exact Rust program that Charon and Aeneas translate.
//!
//! Transformations relative to RustCrypto's ORIGINAL method bodies:
//! 1. Instantiate Gost89<S: Sbox> for S = sboxes::Tc26, used by Magma.
//!    Every S::g(..) becomes sboxes::Tc26::g(..).
//! 2. PRESERVE the original for loops, iteration bounds and key indexing.
//!    Aeneas needs the InOut input copied to eight owned bytes before loops;
//!    this changes input borrowing, not the encryption round computations.
//! 3. Use the small Block/InOut adapter below instead of the original
//!    cipher/hybrid-array API, which Aeneas cannot currently translate.
//!    Equivalence of the adapter to the real cipher API is NOT proved.
//!
//! All other cryptographic expressions (Feistel step, packing, S-box code)
//! come from the original methods. Tests compare this view with upstream
//! RustCrypto and the RFC test vector; testing is NOT a formal proof.
#![allow(dead_code)]
use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
};
// Always compile the ORIGINAL RustCrypto S-box source; no copied S-box tables.
#[path = "../../magma/src/sboxes.rs"]
mod sboxes;
pub use sboxes::Sbox;
use sboxes::SboxExt;

// Verification-only adapter, NOT the implementation of cipher::InOut.
// Model the only operations the original method actually uses:
// get_in() -> borrow the input block; get_out() -> mutable output block,
// indexing 8 bytes, and copying the two 4-byte halves. This definition
// is a proof obligation: it doesn't establish the real cipher semantics.
pub struct Block<T> {
    bytes: [u8; 8],
    marker: PhantomData<T>,
}
impl<T> Block<T> {
    pub fn new(bytes: [u8; 8]) -> Self {
        Self {
            bytes,
            marker: PhantomData,
        }
    }
}
impl<T> Deref for Block<T> {
    type Target = [u8; 8];
    fn deref(&self) -> &Self::Target {
        &self.bytes
    }
}
impl<T> DerefMut for Block<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.bytes
    }
}
pub struct InOut<'a, 'b, T> {
    input: &'a T,
    output: &'b mut T,
}
impl<'a, 'b, T> InOut<'a, 'b, T> {
    pub fn get_in(&self) -> &T {
        self.input
    }
    pub fn get_out(&mut self) -> &mut T {
        self.output
    }
}
pub trait BlockCipherEncBackend: Sized {
    fn encrypt_block(&self, block: InOut<'_, '_, Block<Self>>);
}
pub trait BlockCipherDecBackend: Sized {
    fn decrypt_block(&self, block: InOut<'_, '_, Block<Self>>);
}
pub struct Gost89<S: Sbox> {
    key: [u32; 8],
    _p: PhantomData<S>,
}

// Original (rust/magma/src/lib.rs, BlockCipherEncBackend):
// impl<S: Sbox> BlockCipherEncBackend for Gost89<S> {
//   ... let mut v = (to_u32(&b[0..4]), to_u32(&b[4..8]));
//   for _ in 0..3 {
//       for i in 0..8 { v = (v.1, v.0 ^ S::g(v.1, self.key[i])); }
//   }
//   for i in (0..8).rev() { v = (v.1, v.0 ^ S::g(v.1, self.key[i])); }
//   ... block[0..4].copy_from_slice(&v.1.to_be_bytes()); ...
// }
// Below: the original loops and Feistel expression, specialized S=Tc26.
// InOut::get_in().bytes copies the fixed-size input before the loops.
impl BlockCipherEncBackend for Gost89<sboxes::Tc26> {
    #[inline]
    fn encrypt_block(&self, mut block: InOut<'_, '_, Block<Self>>) {
        let b = block.get_in().bytes;
        let mut v = (to_u32(&b[0..4]), to_u32(&b[4..8]));
        for _ in 0..3 {
            for i in 0..8 {
                v = (v.1, v.0 ^ sboxes::Tc26::g(v.1, self.key[i]));
            }
        }
        for i in (0..8).rev() {
            v = (v.1, v.0 ^ sboxes::Tc26::g(v.1, self.key[i]));
        }
        let block = block.get_out();
        block[0..4].copy_from_slice(&v.1.to_be_bytes());
        block[4..8].copy_from_slice(&v.0.to_be_bytes());
    }
}

// Original (rust/magma/src/lib.rs, BlockCipherDecBackend):
// impl<S: Sbox> BlockCipherDecBackend for Gost89<S> {
//   ... let mut v = (to_u32(&b[0..4]), to_u32(&b[4..8]));
//   for i in 0..8 { v = (v.1, v.0 ^ S::g(v.1, self.key[i])); }
//   for _ in 0..3 {
//       for i in (0..8).rev() { v = (v.1, v.0 ^ S::g(v.1, self.key[i])); }
//   }
//   ... block[0..4].copy_from_slice(&v.1.to_be_bytes()); ...
// }
// Below: the original loops and Feistel expression, specialized S=Tc26.
// InOut::get_in().bytes copies the fixed-size input before the loops.
impl BlockCipherDecBackend for Gost89<sboxes::Tc26> {
    #[inline]
    fn decrypt_block(&self, mut block: InOut<'_, '_, Block<Self>>) {
        let b = block.get_in().bytes;
        let mut v = (to_u32(&b[0..4]), to_u32(&b[4..8]));

        for i in 0..8 {
            v = (v.1, v.0 ^ sboxes::Tc26::g(v.1, self.key[i]));
        }

        for _ in 0..3 {
            for i in (0..8).rev() {
                v = (v.1, v.0 ^ sboxes::Tc26::g(v.1, self.key[i]));
            }
        }
        let block = block.get_out();
        block[0..4].copy_from_slice(&v.1.to_be_bytes());
        block[4..8].copy_from_slice(&v.0.to_be_bytes());
    }
}

#[inline(always)]
fn to_u32(chunk: &[u8]) -> u32 {
    u32::from_be_bytes(chunk.try_into().unwrap())
}

pub fn encrypt_with_words(key: [u32; 8], plain: [u8; 8]) -> [u8; 8] {
    let cipher = Gost89::<sboxes::Tc26> {
        key,
        _p: PhantomData,
    };
    let input = Block::new(plain);
    let mut output = Block::new([0; 8]);
    cipher.encrypt_block(InOut {
        input: &input,
        output: &mut output,
    });
    output.bytes
}
pub fn decrypt_with_words(key: [u32; 8], encrypted: [u8; 8]) -> [u8; 8] {
    let cipher = Gost89::<sboxes::Tc26> {
        key,
        _p: PhantomData,
    };
    let input = Block::new(encrypted);
    let mut output = Block::new([0; 8]);
    cipher.decrypt_block(InOut {
        input: &input,
        output: &mut output,
    });
    output.bytes
}

#[cfg(test)]
mod tests {
    use super::{decrypt_with_words, encrypt_with_words};
    use magma::Magma;
    use magma::cipher::{Array, BlockCipherDecrypt, BlockCipherEncrypt, KeyInit};

    #[test]
    fn compare_upstream_for_256_cases() {
        for seed in 0u32..256 {
            let words: [u32; 8] = core::array::from_fn(|i| {
                seed.wrapping_mul(0x9e37_79b9).rotate_left((i * 3) as u32)
                    ^ (i as u32).wrapping_mul(0xdead_beef)
            });
            let key: [u8; 32] = core::array::from_fn(|i| words[i / 4].to_be_bytes()[i % 4]);
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
            0xffee_ddcc,
            0xbbaa_9988,
            0x7766_5544,
            0x3322_1100,
            0xf0f1_f2f3,
            0xf4f5_f6f7,
            0xf8f9_fafb,
            0xfcfd_feff,
        ];
        let plain = [0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10];
        let cipher = [0x4e, 0xe9, 0x01, 0xe5, 0xc2, 0xd8, 0xca, 0x3d];
        assert_eq!(encrypt_with_words(words, plain), cipher);
        assert_eq!(decrypt_with_words(words, cipher), plain);
    }
}
