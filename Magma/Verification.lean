module

public import Magma.RFC8891
public import Magma.RustCrypto

@[expose] public section

/-!
# RFC 8891 and unmodified RustCrypto

The RFC specification and Aeneas's model of the original RustCrypto S-box
computations are available together. The original encryption/decryption
methods are extracted into full LLBC but not yet translated into Lean.
No equivalence theorem is claimed.
-/

namespace Magma.Verification

#check Magma.encrypt

#check Magma.decrypt

#check RustCrypto.sboxes.SboxExt.g.default

end Magma.Verification
