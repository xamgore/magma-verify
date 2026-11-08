module

public import Magma.Proof.Sbox.Nibbles

@[expose] public section

/-! # Each source-derived Tc26 byte equals two RFC nibble substitutions.

This proves the original expanded-table lookup for every possible 32-bit
input and each of four bytes, in the *same* orientation as RFC 8891.
-/

set_option maxRecDepth 4096
open Aeneas Aeneas.Std Result

namespace Magma.Proof

lemma tc26_byte_matches_rfc (a : Std.U32) (r : Fin 4) :
    ((tc26Expanded.val[r.val]!).val[byteIndex a (rUsize r)]!).bv =
      (Magma.π (hiRow r) (Magma.Internal.nibble a.bv (hiRow r))) ++
        (Magma.π (loRow r) (Magma.Internal.nibble a.bv (loRow r))) := by
  let n := byteIndex a (rUsize r)
  have hn : n < 256 := by
    dsimp only [n]
    rw [byteIndex_extract]
    exact (BitVec.extractLsb' (8 * r.val) 8 a.bv).isLt
  let idx : Fin 256 := ⟨n, hn⟩
  have ht := tc26_expanded_sbox_matches_rfc r idx
  have hnb := byteIndex_nibbles a r
  have hlo : (loCol idx).val = (Magma.Internal.nibble a.bv (loRow r)).toNat := hnb.1.symm
  have hhi : (hiCol idx).val = (Magma.Internal.nibble a.bv (hiRow r)).toNat := hnb.2.symm
  apply BitVec.eq_of_toNat_eq
  change
    (expCell tc26Expanded r idx).val =
      ((Magma.π (hiRow r) (Magma.Internal.nibble a.bv (hiRow r))) ++
          (Magma.π (loRow r) (Magma.Internal.nibble a.bv (loRow r)))).toNat
  rw [BitVec.toNat_append_eq_mul_add, rfc_sbox_value_as_nat (hiRow r),
    rfc_sbox_value_as_nat (loRow r)]
  change
    _ =
      (Magma.π'arrays (hiRow r) ⟨(Magma.Internal.nibble a.bv (hiRow r)).toNat, _⟩).val * 16 +
        (Magma.π'arrays (loRow r) ⟨(Magma.Internal.nibble a.bv (loRow r)).toNat, _⟩).val
  have hloFin :
    (loCol idx) =
      ⟨(Magma.Internal.nibble a.bv (loRow r)).toNat, (Magma.Internal.nibble a.bv (loRow r)).isLt⟩ :=
    Fin.ext hlo
  have hhiFin :
    (hiCol idx) =
      ⟨(Magma.Internal.nibble a.bv (hiRow r)).toNat, (Magma.Internal.nibble a.bv (hiRow r)).isLt⟩ :=
    Fin.ext hhi
  rw [← hhiFin, ← hloFin]
  omega

end Magma.Proof
