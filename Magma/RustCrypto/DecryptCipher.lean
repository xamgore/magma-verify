module

public import Magma.RustCrypto.DecryptLoops

@[expose] public section

/-! The generated decryption key schedule agrees with RFC 8891 for every input. -/

set_option maxRecDepth 4096
open Aeneas Aeneas.Std Result

namespace Magma.RustCrypto

theorem pure_decrypt_32_rounds_match_rfc (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize)
    (l r : BitVec 32) :
    let out := repeatReverse8Rounds key 3 (runKeyRounds key 0 8 (l, r))
    out.2 ++ out.1 = Magma.decrypt (rfcKeyOfWords key) (l ++ r) := by
  simp only [Magma.decrypt, Magma.D, Magma.GStar, Magma.concat]
  simp only [Magma.Internal.split, Magma.substring]
  simp only [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
    rfc_round_key_of_words]
  simp [rustRoundKeyBV, Fin.foldl, repeatReverse8Rounds, runKeyRounds, runReverseRounds, Magma.G,
    Magma.xor]

end Magma.RustCrypto
