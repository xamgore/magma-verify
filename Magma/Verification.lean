module

public import Magma.RFC8891
public import Magma.RustCrypto
public import Magma.RustCrypto.Loops

@[expose] public section

/-!
# RFC 8891 and RustCrypto Tc26

S-box table and 32-bit arithmetic bridges are proved in
`Magma.RustCrypto.Correctness`. The first generated Feistel loop-body step
is related to `Magma.G` in `Magma.RustCrypto.Rounds`.
Executable S-box loop correctness, outer/reverse loop invariants,
and full encryption/decryption equivalence remain open.
-/

namespace Magma.Verification

#check Magma.encrypt

#check Magma.decrypt

#check Magma.RustCrypto.tc26_table_matches_rfc

#check Magma.RustCrypto.tc26_g_if_substitution

#check Magma.RustCrypto.encrypt_inner_step_rfc

#check Magma.RustCrypto.rfc_round_key_of_words

#check Magma.RustCrypto.encrypt_inner_loop_spec

#check RustCryptoTc26.encrypt_with_words

#check RustCryptoTc26.decrypt_with_words

end Magma.Verification
