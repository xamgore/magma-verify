module

public import Magma.RustCrypto.Block

@[expose] public section

/-!
# Complete byte-level refinement to RFC 8891

`encrypt_with_words_if_g` proves the full generated encryption function
returns the byte-encoded RFC ciphertext, for all keys and blocks.
The explicitly stated `g` correctness condition must still be proved from
RustCrypto's expanded S-box generation and substitution loops.
-/

open Aeneas Aeneas.Std Result

namespace Magma.RustCrypto

/-- RFC ciphertext bytes, packed in network order. -/
def rfcEncryptedBytes (key : Aeneas.Std.Array Std.U32 8#usize)
    (plain : Aeneas.Std.Array Std.U8 8#usize) : List Std.U8 :=
  let c := Magma.encrypt (rfcKeyOfWords key)
    (readWord plain 0 ++ readWord plain 4)
  let halves := Magma.Internal.split 32 32 c
  (halves.1.toBEBytes ++ halves.2.toBEBytes).map
    (fun b => (⟨b⟩ : Std.U8))

theorem expected_bytes_are_rfc (key : Aeneas.Std.Array Std.U32 8#usize)
    (plain : Aeneas.Std.Array Std.U8 8#usize) :
    expectEncryptedBytes key plain = rfcEncryptedBytes key plain := by
  let out := runReverseRounds key 0 8 (repeat8Rounds key 3 (readWord plain 0, readWord plain 4))
  have hs :
    Magma.Internal.split 32 32
        (Magma.encrypt (rfcKeyOfWords key) (readWord plain 0 ++ readWord plain 4)) =
      (out.2, out.1) := by
    rw [← pure_32_rounds_match_rfc key (readWord plain 0) (readWord plain 4)]
    exact Magma.concat_split ⟨32, out.2⟩ ⟨32, out.1⟩
  simp only [rfcEncryptedBytes, expectEncryptedBytes]
  rw [hs]

theorem encrypt_with_words_if_g (key : Aeneas.Std.Array Std.U32 8#usize)
    (plain : Aeneas.Std.Array Std.U8 8#usize)
    (hg :
      ∀ a k : Std.U32,
        RustCryptoTc26.sboxes.SboxExt.g.default tc26SboxExt a k =
          ok (⟨Magma.g k.bv a.bv⟩ : Std.U32)) :
    RustCryptoTc26.encrypt_with_words key plain ⦃ out =>
      out.val = rfcEncryptedBytes key plain ⦄ := by
  unfold RustCryptoTc26.encrypt_with_words
  step
    with(encrypt_block_bytes_if_g { key := key, _p := () }
      { input := plain, output := Array.repeat 8#usize 0#u8 } hg)
  exact out_post.trans (expected_bytes_are_rfc key plain)

end Magma.RustCrypto
