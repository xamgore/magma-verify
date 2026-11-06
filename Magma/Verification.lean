module

public import Magma.RFC8891
public import Magma.RustCrypto

@[expose] public section

/-!
# RFC 8891 and unmodified RustCrypto

The RFC specification, original S-box model, and Tc26-specialized
model of the original encrypt/decrypt method bodies are available together.
The specialized bodies are mechanically unrolled and use a simplified
Block/InOut adapter: equivalence with upstream RustCrypto is NOT proved.
-/

namespace Magma.Verification

#check Magma.encrypt

#check Magma.decrypt

#check RustCrypto.sboxes.SboxExt.g.default

#check RustCryptoTc26.encrypt_with_words

#check RustCryptoTc26.decrypt_with_words

end Magma.Verification
