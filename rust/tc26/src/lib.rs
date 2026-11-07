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
//! 3. Replace the cipher::InOut<Block<Self>> boundary with the minimal
//!    InOut<[u8; 8]> borrowing adapter in adapter.rs. There are NO copied
//!    cipher backend traits or Block type. Adapter equivalence remains open.
//!
//! All other cryptographic expressions (Feistel step, packing, S-box code)
//! come from the original methods.
//!
#![allow(dead_code)]
use core::marker::PhantomData;

mod adapter;
use adapter::InOut;
// Always compile the ORIGINAL RustCrypto S-box source; no copied S-box tables.
#[path = "../../magma/src/sboxes.rs"]
mod sboxes;
pub use sboxes::Sbox;
use sboxes::SboxExt;

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
// *block.get_in() copies exactly eight input bytes before the loops.
impl Gost89<sboxes::Tc26> {
    #[inline]
    fn encrypt_block(&self, mut block: InOut<'_, '_, [u8; 8]>) {
        let b = *block.get_in();
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
// *block.get_in() copies exactly eight input bytes before the loops.
impl Gost89<sboxes::Tc26> {
    #[inline]
    fn decrypt_block(&self, mut block: InOut<'_, '_, [u8; 8]>) {
        let b = *block.get_in();
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
    let input = plain;
    let mut output = [0u8; 8];
    cipher.encrypt_block(InOut {
        input: &input,
        output: &mut output,
    });
    output
}
pub fn decrypt_with_words(key: [u32; 8], encrypted: [u8; 8]) -> [u8; 8] {
    let cipher = Gost89::<sboxes::Tc26> {
        key,
        _p: PhantomData,
    };
    let input = encrypted;
    let mut output = [0u8; 8];
    cipher.decrypt_block(InOut {
        input: &input,
        output: &mut output,
    });
    output
}
