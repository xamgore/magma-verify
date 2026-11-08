module

public import Magma.Proof.Encrypt.Cipher

@[expose] public section

/-!
# Original RustCrypto big-endian 4-byte input conversion

Aeneas's source-derived `Magma.Rust.to_u32` is verified to terminate
for four-byte slices and to return the exact big-endian BitVec word.
-/

open Aeneas Aeneas.Std Result

namespace Magma.Proof

def sliceWord (s : Slice Std.U8) (hlen : s.length = 4) : BitVec 32 :=
  (BitVec.fromBEBytes (s.val.map Std.U8.bv)).cast
    (by
      have hh : s.val.length = 4 := by simpa [Slice.length] using hlen
      simp [hh])

lemma to_u32_reads_big_endian_bytes (s : Slice Std.U8) (hlen : s.length = 4) :
    Magma.Rust.to_u32 s ⦃ out => out.bv = sliceWord s hlen ⦄ := by
  unfold Magma.Rust.to_u32
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

end Magma.Proof
