-- Definitional aliases specializing the upstream generic block methods to Tc26.
-- No cryptographic operations are reimplemented here.
module
public import Magma.RustCrypto.Tc26.Funs
@[expose] public section

namespace RustCryptoTc26

abbrev adapter.InOut.get_in := adapter.InOutABArrayU88.get_in

abbrev Gost89Tc26.encrypt_block_loop0_loop0.body :=
  Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0_loop0.body sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

abbrev Gost89Tc26.encrypt_block_loop0_loop0 :=
  Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0_loop0 sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

abbrev Gost89Tc26.encrypt_block_loop0.body :=
  Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0.body sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

abbrev Gost89Tc26.encrypt_block_loop0 :=
  Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0 sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

abbrev Gost89Tc26.encrypt_block_loop1.body :=
  Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop1.body sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

abbrev Gost89Tc26.encrypt_block_loop1 :=
  Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop1 sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

abbrev Gost89Tc26.encrypt_block :=
  Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherEncBackendArrayU88.encrypt_block sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

abbrev Gost89Tc26.decrypt_block_loop0.body :=
  Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop0.body sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

abbrev Gost89Tc26.decrypt_block_loop0 :=
  Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop0 sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

abbrev Gost89Tc26.decrypt_block_loop1_loop0.body :=
  Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1_loop0.body sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

abbrev Gost89Tc26.decrypt_block_loop1_loop0 :=
  Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1_loop0 sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

abbrev Gost89Tc26.decrypt_block_loop1.body :=
  Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1.body sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

abbrev Gost89Tc26.decrypt_block_loop1 :=
  Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1 sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

abbrev Gost89Tc26.decrypt_block :=
  Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherDecBackendArrayU88.decrypt_block sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

end RustCryptoTc26
