#![allow(dead_code)]

//! Minimal safe verification-only interface matching the backend signatures.
use cipher::BlockSizeUser;

pub struct InOut<'a, 'b, T> {
    pub(crate) input: &'a T,
    pub(crate) output: &'b mut T,
}
impl<'a, 'b> InOut<'a, 'b, [u8; 8]> {
    pub fn get_in(&self) -> [u8; 8] {
        *self.input
    }
}
impl<'a, 'b, T> InOut<'a, 'b, T> {
    pub fn get_out(&mut self) -> &mut T {
        self.output
    }
}

pub trait VerifyBlock {
    type Block: Copy;
}
impl<T> VerifyBlock for T {
    type Block = [u8; 8];
}
pub type Block<T> = <T as VerifyBlock>::Block;

pub trait BlockCipherEncBackend: VerifyBlock {
    fn encrypt_block(&self, block: InOut<'_, '_, Block<Self>>);
}
pub trait BlockCipherDecBackend: VerifyBlock {
    fn decrypt_block(&self, block: InOut<'_, '_, Block<Self>>);
}
pub trait BlockCipherEncClosure: BlockSizeUser {
    fn call<B: BlockCipherEncBackend + BlockSizeUser<BlockSize = Self::BlockSize>>(
        self,
        backend: &B,
    );
}
pub trait BlockCipherDecClosure: BlockSizeUser {
    fn call<B: BlockCipherDecBackend + BlockSizeUser<BlockSize = Self::BlockSize>>(
        self,
        backend: &B,
    );
}
pub trait BlockCipherEncrypt: BlockSizeUser + Sized {
    fn encrypt_with_backend(&self, f: impl BlockCipherEncClosure<BlockSize = Self::BlockSize>);
}
pub trait BlockCipherDecrypt: BlockSizeUser {
    fn decrypt_with_backend(&self, f: impl BlockCipherDecClosure<BlockSize = Self::BlockSize>);
}

// Monomorphic roots tell Charon to translate Tc26, not the other S-box variants.
pub fn verify_encrypt(
    self_: &crate::Gost89<crate::sboxes::Tc26>,
    block: InOut<'_, '_, Block<crate::Gost89<crate::sboxes::Tc26>>>,
) {
    <crate::Gost89<crate::sboxes::Tc26> as BlockCipherEncBackend>::encrypt_block(self_, block)
}
pub fn verify_decrypt(
    self_: &crate::Gost89<crate::sboxes::Tc26>,
    block: InOut<'_, '_, Block<crate::Gost89<crate::sboxes::Tc26>>>,
) {
    <crate::Gost89<crate::sboxes::Tc26> as BlockCipherDecBackend>::decrypt_block(self_, block)
}

// A safe fixed-size key interface avoids hybrid-array's generic associated types.
pub trait KeyInit: Sized {
    fn new(key: &[u8; 32]) -> Self;
}

pub fn verify_key_init(key: &[u8; 32]) -> crate::Gost89<crate::sboxes::Tc26> {
    <crate::Gost89<crate::sboxes::Tc26> as KeyInit>::new(key)
}
