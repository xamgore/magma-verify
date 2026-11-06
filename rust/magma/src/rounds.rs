//! Cipher-independent core called by RustCrypto's block-cipher backend.
//! This is the production round path, not a duplicate verification model.

use crate::sboxes::{Sbox, SboxExt};

#[inline]
fn split_block(block: [u8; 8]) -> (u32, u32) {
    (
        u32::from_be_bytes([block[0], block[1], block[2], block[3]]),
        u32::from_be_bytes([block[4], block[5], block[6], block[7]]),
    )
}

#[inline]
fn join_block(v: (u32, u32)) -> [u8; 8] {
    let a = v.1.to_be_bytes();
    let b = v.0.to_be_bytes();
    [a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]]
}

#[inline]
fn encrypt_schedule<S: Sbox>(key: &[u32; 8], v: (u32, u32), round: u32) -> (u32, u32) {
    if round == 32 {
        return v;
    }
    let key_index = if round < 24 {
        (round % 8) as usize
    } else {
        (31 - round) as usize
    };
    let next = (v.1, v.0 ^ S::g(v.1, key[key_index]));
    encrypt_schedule::<S>(key, next, round + 1)
}

#[inline]
fn decrypt_schedule<S: Sbox>(key: &[u32; 8], v: (u32, u32), round: u32) -> (u32, u32) {
    if round == 32 {
        return v;
    }
    let key_index = if round < 8 {
        round as usize
    } else {
        (7 - ((round - 8) % 8)) as usize
    };
    let next = (v.1, v.0 ^ S::g(v.1, key[key_index]));
    decrypt_schedule::<S>(key, next, round + 1)
}

/// Encrypt one 64-bit block with exactly 32 Feistel rounds.
pub(crate) fn encrypt_block_core<S: Sbox>(key: &[u32; 8], block: [u8; 8]) -> [u8; 8] {
    join_block(encrypt_schedule::<S>(key, split_block(block), 0))
}

/// Decrypt one 64-bit block with the inverse subkey schedule.
pub(crate) fn decrypt_block_core<S: Sbox>(key: &[u32; 8], block: [u8; 8]) -> [u8; 8] {
    join_block(decrypt_schedule::<S>(key, split_block(block), 0))
}
