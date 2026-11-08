-- Tc26 instantiation of the generic RustCrypto block backend.
-- These definitions specialize the extracted generic Rust methods, not their algorithm.
module
public import Magma.Rust.Funs

@[expose] public section

namespace Magma.Proof

abbrev Tc26.encrypt_block_loop0_loop0.body :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0_loop0.body
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.encrypt_block_loop0_loop0 :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0_loop0
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.encrypt_block_loop0.body :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0.body
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.encrypt_block_loop0 :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.encrypt_block_loop1.body :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop1.body
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.encrypt_block_loop1 :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop1
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.encrypt_block :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.decrypt_block_loop0.body :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop0.body
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.decrypt_block_loop0 :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop0
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.decrypt_block_loop1_loop0.body :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1_loop0.body
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.decrypt_block_loop1_loop0 :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1_loop0
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.decrypt_block_loop1.body :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1.body
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.decrypt_block_loop1 :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.decrypt_block :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

end Magma.Proof
