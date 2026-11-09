-- Specialize the extracted generic block methods to the concrete S-box.
-- The original Feistel operations remain defined in the generated Rust model.
module
public import Magma.Rust.Funs

@[expose] public section

namespace Magma.Rust

abbrev encrypt_block_loop0_loop0.body :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0_loop0.body
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev encrypt_block_loop0_loop0 :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0_loop0
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev encrypt_block_loop0.body :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0.body
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev encrypt_block_loop0 :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev encrypt_block_loop1.body :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop1.body
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev encrypt_block_loop1 :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop1
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev encrypt_block :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev decrypt_block_loop0.body :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop0.body
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev decrypt_block_loop0 :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop0
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev decrypt_block_loop1_loop0.body :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1_loop0.body
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev decrypt_block_loop1_loop0 :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1_loop0
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev decrypt_block_loop1.body :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1.body
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev decrypt_block_loop1 :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

abbrev decrypt_block :=
  Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

end Magma.Rust
