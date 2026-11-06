module

public import Magma.RFC8891
public import RustCrypto.Code.Funs

@[expose] public section

/-!
# RFC 8891 and unmodified RustCrypto

This module brings the RFC specification together with Aeneas's model
of RustCrypto's original S-box computations. The original encrypt/decrypt
methods are present in the full Charon LLBC, not yet translated to Lean.
No equivalence theorem is claimed.
-/

namespace Magma.Verification

#check Magma.encrypt

#check Magma.decrypt

#check RustCrypto.sboxes.SboxExt.g.default

end Magma.Verification
