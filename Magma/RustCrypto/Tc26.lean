-- Tc26 instantiation of the generic RustCrypto block backend.
-- These definitions specialize the extracted generic Rust methods, not their algorithm.
module
public import Magma.RustCrypto.Tc26.Funs

@[expose] public section

namespace RustCryptoTc26

abbrev Tc26.encrypt_block_loop0_loop0.body :=
  Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0_loop0.body
    sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.encrypt_block_loop0_loop0 :=
  Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0_loop0
    sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.encrypt_block_loop0.body :=
  Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0.body
    sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.encrypt_block_loop0 :=
  Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0
    sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.encrypt_block_loop1.body :=
  Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop1.body
    sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.encrypt_block_loop1 :=
  Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop1
    sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.encrypt_block :=
  Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block
    sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.decrypt_block_loop0.body :=
  Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop0.body
    sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.decrypt_block_loop0 :=
  Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop0
    sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.decrypt_block_loop1_loop0.body :=
  Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1_loop0.body
    sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.decrypt_block_loop1_loop0 :=
  Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1_loop0
    sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.decrypt_block_loop1.body :=
  Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1.body
    sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.decrypt_block_loop1 :=
  Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1
    sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev Tc26.decrypt_block :=
  Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block
    sboxes.Tc26.Insts.MagmaSboxesSbox

end RustCryptoTc26
