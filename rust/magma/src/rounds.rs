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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sboxes::Tc26;

    // Previous implementation, retained as a regression oracle for the refactor.
    fn old_encrypt(key: &[u32; 8], block: [u8; 8]) -> [u8; 8] {
        let mut v = split_block(block);
        for _ in 0..3 {
            for i in 0..8 {
                v = (v.1, v.0 ^ Tc26::g(v.1, key[i]));
            }
        }
        for i in (0..8).rev() {
            v = (v.1, v.0 ^ Tc26::g(v.1, key[i]));
        }
        join_block(v)
    }

    fn old_decrypt(key: &[u32; 8], block: [u8; 8]) -> [u8; 8] {
        let mut v = split_block(block);
        for i in 0..8 {
            v = (v.1, v.0 ^ Tc26::g(v.1, key[i]));
        }
        for _ in 0..3 {
            for i in (0..8).rev() {
                v = (v.1, v.0 ^ Tc26::g(v.1, key[i]));
            }
        }
        join_block(v)
    }

    #[test]
    fn round_core_matches_original_for_sampled_inputs() {
        for seed in 0u32..128 {
            let key: [u32; 8] = core::array::from_fn(|i| {
                (seed + 1)
                    .wrapping_mul(0x9e37_79b9)
                    .rotate_left((i * 3) as u32)
                    ^ (i as u32).wrapping_mul(0xdead_beef)
            });
            let block = (seed.wrapping_mul(0x517c_c1b7) as u64)
                .wrapping_mul(0x0102_0304_0506_0709)
                .to_be_bytes();
            let ciphertext = encrypt_block_core::<Tc26>(&key, block);
            assert_eq!(ciphertext, old_encrypt(&key, block));
            assert_eq!(decrypt_block_core::<Tc26>(&key, ciphertext), block);
            assert_eq!(
                decrypt_block_core::<Tc26>(&key, ciphertext),
                old_decrypt(&key, ciphertext)
            );
        }
    }

    #[test]
    fn rfc_8891_vector_at_round_core() {
        let key = [
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
        let expected = [0x4e, 0xe9, 0x01, 0xe5, 0xc2, 0xd8, 0xca, 0x3d];
        assert_eq!(encrypt_block_core::<Tc26>(&key, plain), expected);
        assert_eq!(decrypt_block_core::<Tc26>(&key, expected), plain);
    }
}
