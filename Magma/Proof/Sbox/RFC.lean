module

public import Magma.Proof.Sbox.Prefix

@[expose] public section

/-!
# Expanded RustCrypto bytes equal pairs of RFC 8891 nibble substitutions

Each generated expanded byte's numeric value equals the RFC
substitution for the corresponding lower and upper nibble.
Also supplies the standard RFC ZMod/BitVec nibble identity.
-/

open Aeneas Aeneas.Std Result

namespace Magma.Proof

def loRow (r : Fin 4) : Fin 8 :=
  ⟨2 * r.val, by omega⟩

def hiRow (r : Fin 4) : Fin 8 :=
  ⟨2 * r.val + 1, by omega⟩

def loCol (c : Fin 256) : Fin 16 :=
  ⟨c.val % 16, Nat.mod_lt _ (by decide)⟩

def hiCol (c : Fin 256) : Fin 16 :=
  ⟨c.val / 16, by omega⟩

lemma expectedExpByte_matches_rfc (r : Fin 4) (c : Fin 256) :
    (expectedExpByte rustSboxTable r c).val =
      (Magma.π'arrays (loRow r) (loCol c)).val + 16 * (Magma.π'arrays (hiRow r) (hiCol c)).val := by
  let lo := (rustSboxTable.val[2 * r.val]!).val[c.val % 16]!
  let hi := (rustSboxTable.val[2 * r.val + 1]!).val[c.val / 16]!
  have hlo : lo.val = (Magma.π'arrays (loRow r) (loCol c)).val :=
    rust_table_matches_rfc (loRow r) (loCol c)
  have hhi : hi.val = (Magma.π'arrays (hiRow r) (hiCol c)).val :=
    rust_table_matches_rfc (hiRow r) (hiCol c)
  have hloBound : lo.val < 16 := rust_sbox_entries_lt16 (loRow r) (loCol c)
  have hhiBound : hi.val < 16 := rust_sbox_entries_lt16 (hiRow r) (hiCol c)
  change (lo.bv + (hi.bv <<< 4)).toNat = _
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  change (lo.val + (hi.val * 16) % 256) % 256 = _
  have hh : hi.val * 16 < 256 := by omega
  rw [Nat.mod_eq_of_lt hh]
  have hsum : lo.val + hi.val * 16 < 256 := by omega
  rw [Nat.mod_eq_of_lt hsum]
  rw [hlo, hhi]
  omega

theorem rust_expanded_sbox_matches_rfc (r : Fin 4) (c : Fin 256) :
    (expCell rustExpandedSbox r c).val =
      (Magma.π'arrays (loRow r) (loCol c)).val + 16 * (Magma.π'arrays (hiRow r) (hiCol c)).val := by
  rw [rust_expanded_table_cell_correct]
  exact expectedExpByte_matches_rfc r c

lemma rfc_sbox_value_as_nat (i : Fin 8) (v : BitVec 4) :
    (Magma.π i v).toNat = (Magma.π'arrays i ⟨v.toNat, v.isLt⟩).val := by
  have hfin : (ZMod.finEquiv 16).symm (v.toNat : ZMod 16) = v.toFin := by
    apply Fin.ext
    change (v.toNat : ZMod 16).val = v.toNat
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt v.isLt]
  change
    (BitVec.ofNat 4 (Magma.π'arrays i ((ZMod.finEquiv 16).symm (v.toNat : ZMod 16))).val).toNat =
      (Magma.π'arrays i v.toFin).val
  rw [hfin, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (ZMod.val_lt (Magma.π'arrays i v.toFin))

lemma rfc_sbox_value_as_bitvec (i : Fin 8) (v : BitVec 4) :
    Magma.π i v = BitVec.ofNat 4 (Magma.π'arrays i ⟨v.toNat, v.isLt⟩).val := by
  apply BitVec.eq_of_toNat_eq
  rw [rfc_sbox_value_as_nat, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (ZMod.val_lt (Magma.π'arrays i v.toFin))).symm

end Magma.Proof
