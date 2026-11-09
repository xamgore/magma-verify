module

public import Magma.Proof.Encrypt.Block

@[expose] public section

/-!
# Byte encoding of the RFC 8891 ciphertext

The pure encryption rounds agree with the RFC byte order. The final theorem
for the original block method is in SboxFinal.lean.
-/

open Aeneas Aeneas.Std Result

namespace Magma.Proof

/-- RFC ciphertext bytes, packed in network order. -/
def rfcEncryptedBytes (key : Aeneas.Std.Array Std.U32 8#usize) (plain : Aeneas.Std.Array Std.U8 8#usize) : List Std.U8 :=
  let c := Magma.encrypt (rfcKeyOfWords key) (readWord plain 0 ++ readWord plain 4)
  let halves := Magma.Internal.split 32 32 c
  (halves.1.toBEBytes ++ halves.2.toBEBytes).map (fun b => (⟨b⟩ : Std.U8))

lemma encrypted_bytes_match_rfc (key : Aeneas.Std.Array Std.U32 8#usize)
    (plain : Aeneas.Std.Array Std.U8 8#usize) :
    expectEncryptedBytes key plain = rfcEncryptedBytes key plain := by
  let out := runReverseRounds key 0 8 (repeat8Rounds key 3 (readWord plain 0, readWord plain 4))
  have hs :
    Magma.Internal.split 32 32
        (Magma.encrypt (rfcKeyOfWords key) (readWord plain 0 ++ readWord plain 4)) =
      (out.2, out.1) := by
    rw [← encrypt_round_schedule_matches_rfc key (readWord plain 0) (readWord plain 4)]
    exact Magma.concat_split ⟨32, out.2⟩ ⟨32, out.1⟩
  simp only [rfcEncryptedBytes, expectEncryptedBytes]
  rw [hs]

end Magma.Proof
