module

public import Magma.RFC8891
public import RustCrypto.Code.Funs

@[expose] public section

/-!
# RustCrypto Magma verification boundary

The RFC 8891 specification and the Aeneas-translated production round
core are available in this module under the same Lean toolchain.
No theorem asserting their equality has been proved yet.

The next task is to relate Aeneas's byte arrays and key-word arrays
to `Magma.V 64` and `Magma.V 256`, then prove the round schedule and
S-box agreement and successful termination of the translated recursion.
-/

namespace Magma.Verification

#check RustCrypto.rounds.encrypt_block_core

#check RustCrypto.rounds.decrypt_block_core

#check Magma.encrypt

#check Magma.decrypt

end Magma.Verification
