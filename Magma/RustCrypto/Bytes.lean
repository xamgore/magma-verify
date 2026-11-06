module

public import Magma.RustCrypto.Cipher

@[expose] public section

/-!
# Original RustCrypto big-endian 4-byte input conversion

Aeneas's source-derived `RustCryptoTc26.to_u32` is verified to terminate
for four-byte slices and to return the exact big-endian BitVec word.
-/

open Aeneas Aeneas.Std Result

namespace Magma.RustCrypto

def sliceWord (s : Slice Std.U8) (hlen : s.length = 4) : BitVec 32 :=
  (BitVec.fromBEBytes (s.val.map Std.U8.bv)).cast
    (by
      have hh : s.val.length = 4 := by simpa [Slice.length] using hlen
      simp [hh])

theorem to_u32_spec (s : Slice Std.U8) (hlen : s.length = 4) :
    RustCryptoTc26.to_u32 s ⦃ out => out.bv = sliceWord s hlen ⦄ := by
  unfold RustCryptoTc26.to_u32
  step*
  case h =>
    cases r with
    | Ok v => exact ⟨v, rfl⟩
    | Err e =>
      simp at r_post; exact False.elim (r_post hlen)
  all_goals
    have hv : a.val = s.val := by simp_all
    change
      (BitVec.fromBEBytes (a.val.map U8.bv)).cast (by simp [a.property]) =
        (BitVec.fromBEBytes (s.val.map U8.bv)).cast
          (by
            have hs : s.val.length = 4 := by simpa [Slice.length] using hlen
            simp [hs])
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_cast]
    rw [hv]

end Magma.RustCrypto
