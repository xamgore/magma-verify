module

-- A formalization of the Magma block cipher specified in RFC 8891 using Lean 4 and Mathlib,
-- including machine-checked proofs of encryption/decryption invertibility and conformance
-- tests against the published test vectors.
--
-- https://www.rfc-editor.org/info/rfc8891/

public import Std
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.BitVec
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.FinCases
public import Batteries.Data.Nat.Lemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Tactic.IrreducibleDef
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Basic
import all Init.Data.Range.Basic

@[expose] public section

/-!
# RFC 8891 specification and verification

The specified representations, transformations, key schedule, encryption and
decryption, together with their invertibility proofs and RFC test data.
Reusable implementation details live in `Magma.Internal`; file-local proof
helpers remain private.
-/

namespace Magma.Internal
end Magma.Internal

open Magma.Internal

namespace Magma

-----------------------------------------------------------------
-- RFC 8891, Section 3.2 Notation
-----------------------------------------------------------------

/--
  `V*` is the set of all binary vector strings of a finite length, including
  the empty string.

  Lean's `BitVec` type by definition is a bitvector of the specified width.
  A set of all bitvectors of a finite length is described by a dependent tuple (Sigma-type).
-/
def VStar : Type := Σ s : Nat, BitVec s

def emptyStr : VStar :=
  ⟨0, 0#0⟩

/--
  `V_s` is the set of all binary strings of length `s`, where `s` is a nonnegative integer.
  Substrings and string components are enumerated from right to left, starting from zero.

  Lean's `BitVec` type by definition is a bitvector of the specified width.
  Which fits the interpretation.
-/
abbrev V (s : Nat) : Type := BitVec s

/--
  Returns the `i`-th component, indexed from right to left,
  starting from zero, as specified by RFC 8891 §3.2.
-/
def component {s : Nat} (str : V s) (i : Fin s) : Bool :=
  str.getLsb i

/--
  Extracts a substring of length `take` starting at position `offset`, counting from right to left.

  The substring must fit within the original string.
-/
def substring
  {s : Nat} (str : V s)
  {offset : Nat} {take : Nat} (_range : offset + take ≤ s)
  : V take :=
    BitVec.extractLsb' offset take str

/--
  The i-th component of a substring is the (offset + i)-th component of the original string.
-/
theorem substring_components_are_string_components
  {s : Nat} (str : V s)
  (offset : Nat) (take : Nat) (range : offset + take ≤ s)
  (i : Fin take)
  : component (substring str range) i = component str ⟨offset + i.val, by omega⟩ := by
    have hi : offset + i.val < s := by omega
    simp [component, substring, BitVec.getLsbD_eq_getElem hi]

/--
  `∣A∣` denotes the number of components (the length) of a string `A` belonging to `V*`.
  (if `A` is an empty string, then `∣A∣ = 0`).
 -/
def length (A : VStar) : Nat := A.1

theorem empty_string_has_zero_length : length emptyStr = 0 :=
  rfl

/--
  Concatenation `A ‖ B` of strings A and B both belonging to `V*` i.e.,
  a string from V_(∣A∣+∣B∣), where the left substring from V_∣A∣
  is equal to A and the right substring from V_∣B∣ is equal to B.
-/
def concat (A B : VStar) : VStar := ⟨length A + length B, A.2 ++ B.2⟩

/-- Length of A ‖ B = ∣A∣ + ∣B∣. -/
theorem length_concat (A B : VStar) :
    length (concat A B) = length A + length B := by
  rfl

/-- Splits a binary string into a left part of length `l` and a right part of length `r`. -/
def Internal.split (l r : Nat) (x : V (l + r)) : V l × V r :=
  (substring x (offset := r) (take := l) (by omega),
   substring x (offset := 0) (take := r) (by omega))

/-- Splitting `A ‖ B` into parts of lengths `∣A∣` and `∣B∣` recovers the original strings. -/
theorem concat_split (A B : VStar) :
    split (length A) (length B) (concat A B).2 = (A.2, B.2) := by
  rcases A with ⟨l, a⟩
  rcases B with ⟨r, b⟩
  simp [split, substring, concat, length,
        BitVec.extractLsb'_append_eq_left,
        BitVec.extractLsb'_append_eq_right]

private def join (l r : Nat) (p : V l × V r) : V (l + r) :=
  p.1 ++ p.2

/-- Splitting and concating binary strings of fixed lengths are mutually inverse. -/
private def splitEquiv (l r : Nat) : V (l + r) ≃ V l × V r where
  toFun := split l r
  invFun := fun p => (concat ⟨l, p.1⟩ ⟨r, p.2⟩).2
  left_inv := by
    intro x
    exact BitVec.extractLsb'_append_extractLsb'
  right_inv := by
    intro x
    exact concat_split ⟨l, x.1⟩ ⟨r, x.2⟩

/--
  Cyclic rotation of string A belonging to V_32 by 11 components
  in the direction of components having greater indices.
-/
def rot11 (str: V 32) : V 32 := str.rotateLeft 11

/--
  Cyclic rotation moves each component 11 positions towards greater indices.
  RFC 8891, Section 3.2.

  As we are working with V_32 those indices are wrapping around modulo 32.
-/
theorem rot11_moves_components_up (str : V 32) (i : Fin 32) :
    component (rot11 str) (i + 11) = component str i := by
  change
    (str.rotateLeft 11).getLsbD ((i.val + 11) % 32) = str.getLsbD i.val
  rw [BitVec.getLsbD_rotateLeft_of_le (by decide : 11 < 32)]
  split_ifs with h
  · have hidx : 32 - 11 + ((i.val + 11) % 32) = i.val := by omega
    simp only [hidx]
  · have hbound : (i.val + 11) % 32 < 32 := by omega
    have hidx : ((i.val + 11) % 32) - 11 = i.val := by omega
    simp [hbound, hidx]

/--
  Cyclic rotation by 11 is equivalent to splitting
  a 32-bit string into 11 high bits and 21 low bits,
  then concatenating them in reverse order.
-/
private theorem rot11_as_split_concat (str : V 32) :
    let (left, right) := split 11 21 str
    rot11 str = (concat ⟨21, right⟩ ⟨11, left⟩).2 := by
  change
    str.rotateLeft 11 =
      BitVec.extractLsb' 0 21 str ++ BitVec.extractLsb' 21 11 str
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateLeft_of_le (by decide : 11 < 32), BitVec.getLsbD_append]
  by_cases h : i < 11
  · simp [h]
  · have hbound : i - 11 < 21 := by omega
    simp [h, hi, hbound]

/-- Cyclic rotation by 11 components is bijective. -/
theorem Internal.rot11_is_bijective : Function.Bijective rot11 := by
  have : Finite (V 32) :=
    Finite.intro ((BitVec.equivFin (m := 32)).toEquiv)
  apply Finite.injective_iff_bijective.mp
  intro a b hab
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin 32 := ⟨j, hj⟩
  change component a i = component b i
  calc
    component a i = component (rot11 a) (i + 11) :=
      (rot11_moves_components_up a i).symm
    _ = component (rot11 b) (i + 11) :=
      congrArg (fun z : V 32 => component z (i + 11)) hab
    _ = component b i := rot11_moves_components_up b i

/-- Exclusive-or of two binary strings of the same length. -/
def xor {s : Nat} (a b : V s) := a.xor b

/-- Each component of the XOR of two strings is the Boolean XOR of their corresponding components. -/
theorem xor_components {s : Nat} (a b : V s) (i : Fin s) :
    component (xor a b) i = Bool.xor (component a i) (component b i) := by
  change
    (xor a b).getLsbD i.val = Bool.xor (a.getLsbD i.val) (b.getLsbD i.val)
  exact BitVec.getLsbD_xor

/--
  Applying XOR with the same string twice recovers the original string.
-/
theorem Internal.xor_cancel_twice (a b : V 32) :
    xor a (xor a b) = b := by
  change a ^^^ (a ^^^ b) = b
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/--
  The ring of residue classes modulo `2^n` (RFC 8891, Section 3.2).

  Mathlib's `ZMod` already has the standard commutative ring structure:
  both addition and multiplication are taken modulo `2^n`. The RFC
  introduces notation `[+]` for addition because the Magma round function
  uses that operation; it does not use ring multiplication.
-/
abbrev Z2 (n : Nat) : Type := ZMod (2 ^ n)

/-- Addition in the ring Z_(2^32). -/
def add₃₂ (a b : Z2 32) : Z2 32 := a + b

/-- Addition of a fixed residue modulo 2^32 is bijective. -/
private theorem add₃₂_is_bijective (k : Z2 32) :
    Function.Bijective (fun a : Z2 32 => add₃₂ a k) := by
  constructor
  · intro a b h
    exact add_right_cancel h
  · intro b
    refine ⟨b - k, ?_⟩
    change (b - k) + k = b
    exact sub_add_cancel b k

/-- The ring structure required by RFC 8891 is already provided by `ZMod`. -/
example (n : Nat) : CommRing (Z2 n) := inferInstance

/-- Maps an element of Z_(2^s) to its binary representation in V_s. -/
def Vec_s (s : Nat) (z : Z2 s) : V s := BitVec.ofNat s z.val

/--
  Maps a binary string in V_s to its corresponding residue in Z_(2^s).

  This is the inverse of Vec_s.
-/
def Int_s (s : Nat) (str : V s) : Z2 s := (str.toNat : Z2 s)

/--
  A finite binary sequence represents the sum
  of its bits weighted by powers of two.
-/
private theorem ofBits_eq_weighted_sum :
    ∀ (s : Nat) (f : Fin s → Bool),
      Nat.ofBits f =
        ∑ i : Fin s, (f i).toNat * 2 ^ i.val := by
  intro s
  induction s with
  | zero =>
      intro f
      simp [Nat.ofBits_zero]
  | succ s ih =>
      intro f
      rw [Nat.ofBits_succ, Fin.sum_univ_succ]
      rw [ih (f ∘ Fin.succ)]
      simp only [Fin.val_zero, pow_zero, mul_one,
                 Fin.val_succ, pow_succ]
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      ac_rfl

/--
  Int_s interprets the components of a binary
  string as a little-endian binary number.
-/
private theorem Int_s_eq_ofBits
    (s : Nat) (str : V s) :
    ZMod.val (Int_s s str) =
      Nat.ofBits (fun i : Fin s => component str i) := by
  have hval :
      ZMod.val (Int_s s str) = str.toNat := by
    change ZMod.val (str.toNat : ZMod (2 ^ s)) = str.toNat
    exact ZMod.val_natCast_of_lt str.toFin.isLt

  have hbits :
      Nat.ofBits (fun i : Fin s => component str i) =
        str.toNat := by
    change
      Nat.ofBits (fun i : Fin s => str.toNat.testBit i.val) =
        str.toNat
    rw [Nat.ofBits_testBit]
    exact Nat.mod_eq_of_lt str.toFin.isLt

  exact hval.trans hbits.symm

/--
  The integer representation of a binary string
  is the sum of its components weighted by their
  corresponding powers of two.

  Int_s(A) = Σᵢ Aᵢ · 2ⁱ
-/
theorem Int_s_binary_representation
    (s : Nat) (str : V s) :
    ZMod.val (Int_s s str) =
      ∑ i : Fin s, (component str i).toNat * 2 ^ i.val := by
  calc
    ZMod.val (Int_s s str) =
        Nat.ofBits (fun i : Fin s => component str i) :=
      Int_s_eq_ofBits s str
    _ = _ :=
      ofBits_eq_weighted_sum s
        (fun i => component str i)

/--
  Vec_s preserves the canonical numeric
  representative of the residue.
-/
private theorem Vec_s_toNat (s : Nat) (z : Z2 s) : (Vec_s s z).toNat = z.val := by
  rw [Vec_s, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (z.val_lt)

/-- Int_s is a left inverse of Vec_s. -/
theorem Internal.Int_s_Vec_s (s : Nat) (z : Z2 s) : Int_s s (Vec_s s z) = z := by
  change ((BitVec.ofNat s z.val).toNat : Z2 s) = z
  rw [BitVec.toNat_ofNat, ZMod.natCast_mod]
  exact ZMod.natCast_zmod_val z

/--
  Vec_s represents every residue using the binary
  expansion specified by RFC 8891, Section 3.2.
-/
theorem Vec_s_binary_representation
    (s : Nat) (z : Z2 s) :
    ZMod.val z =
      ∑ i : Fin s,
        (component (Vec_s s z) i).toNat * 2 ^ i.val := by
  calc
    ZMod.val z =
        ZMod.val (Int_s s (Vec_s s z)) :=
      congrArg ZMod.val (Int_s_Vec_s s z).symm
    _ = _ :=
      Int_s_binary_representation s (Vec_s s z)

/-- Vec_s is a left inverse of Int_s. -/
private theorem Vec_s_Int_s (s : Nat) (str : V s) : Vec_s s (Int_s s str) = str := by
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat s ((str.toNat : Z2 s).val)).toNat = str.toNat
  rw [BitVec.toNat_ofNat, ZMod.val_natCast]
  have h : str.toNat < 2 ^ s := str.toFin.isLt
  simp [Nat.mod_eq_of_lt h]

/-- Bijective correspondence between ring Z_(2^s) and its binary representation. -/
def vecEquiv (s : Nat) : Z2 s ≃ V s where
  toFun := Vec_s s
  invFun := Int_s s
  left_inv := Int_s_Vec_s s
  right_inv := Vec_s_Int_s s

-----------------------------------------------------------------
-- RFC 8891, Section 4.1. Nonlinear Bijection
-----------------------------------------------------------------

/--
  The eight substitution arrays Pi'_i. Each row represents:
  (Pi'_i(0), Pi'_i(1), ..., Pi'_i(15)).
-/
def π'arrays : Fin 8 → Fin 16 → Z2 4 := ![
  ![12, 4, 6, 2, 10, 5, 11, 9, 14, 8, 13, 7, 0, 3, 15, 1],
  ![6, 8, 2, 3, 9, 10, 5, 12, 1, 14, 4, 7, 11, 13, 0, 15],
  ![11, 3, 5, 8, 2, 15, 10, 13, 14, 1, 7, 4, 12, 9, 6, 0],
  ![12, 8, 2, 1, 13, 4, 15, 6, 7, 0, 10, 5, 3, 14, 9, 11],
  ![7, 15, 5, 10, 8, 1, 6, 13, 0, 9, 3, 14, 11, 4, 2, 12],
  ![5, 13, 15, 6, 9, 2, 12, 10, 11, 7, 8, 1, 4, 3, 14, 0],
  ![8, 14, 2, 5, 6, 9, 1, 12, 15, 4, 11, 0, 13, 10, 3, 7],
  ![1, 7, 14, 13, 0, 5, 8, 3, 4, 15, 10, 6, 9, 12, 11, 2]
]

/-- Every substitution table is a bijection on the set of sixteen possible values. -/
theorem π'array_is_substitution (i : Fin 8) :
    Function.Bijective (π'arrays i) := by
  apply Finite.injective_iff_bijective.mp
  apply (Fintype.nodup_map_univ_iff_injective (f := π'arrays i)).mp
  fin_cases i <;> decide

/--
  Pi'\_i : Z_(2^4) -> Z_(2^4).

  The i-th substitution.
-/
def π' (i : Fin 8) (z : Z2 4) : Z2 4 :=
  π'arrays i ((ZMod.finEquiv 16).symm z)

/--
  Every Pi'\_i is bijective on Z_(2^4).
-/
theorem π'_is_bijective (i : Fin 8) :
    Function.Bijective (π' i) := by
  change Function.Bijective
    ((ZMod.finEquiv 16) ∘ (π'arrays i ∘ (ZMod.finEquiv 16).symm))
  exact (ZMod.finEquiv 16).bijective.comp
    ((π'array_is_substitution i).comp (ZMod.finEquiv 16).symm.bijective)

/--
  Pi_i = Vec_4 ∘ Pi'_i ∘ Int_4.
-/
def π (i : Fin 8) (str : V 4) : V 4 :=
  Vec_s 4 (π' i (Int_s 4 str))

/--
  Every Pi_i is a bijection from V_4 to V_4.
-/
theorem π_is_bijective (i : Fin 8) :
    Function.Bijective (π i) := by
  change Function.Bijective
    ((vecEquiv 4) ∘ (π' i ∘ (vecEquiv 4).symm))
  exact (vecEquiv 4).bijective.comp
    ((π'_is_bijective i).comp (vecEquiv 4).symm.bijective)

noncomputable def πEquiv (i : Fin 8) : V 4 ≃ V 4 :=
  Equiv.ofBijective (π i) (π_is_bijective i)

-----------------------------------------------------------------
-- RFC 8891, Section 4.2. Transformations
-----------------------------------------------------------------

/--
  Returns the i-th four-bit component of a 32-bit string, counted from right to left.

  a = a₇ || a₆ || ... || a₀
-/
def Internal.nibble (a : V 32) (i : Fin 8) : V 4 :=
  substring a (offset := 4 * i.val) (take := 4) (by omega)

/--
  t : V₃₂ → V₃₂

  t(a₇ || ... || a₀) = π₇(a₇) || ... || π₀(a₀).
-/
def t (a : V 32) : V 32 :=
  π 7 (nibble a 7) ++
  π 6 (nibble a 6) ++
  π 5 (nibble a 5) ++
  π 4 (nibble a 4) ++
  π 3 (nibble a 3) ++
  π 2 (nibble a 2) ++
  π 1 (nibble a 1) ++
  π 0 (nibble a 0)

example : t 0xfdb97531 = 0x2a196f34 := by decide

example : t 0x2a196f34 = 0xebd9f03a := by decide

example : t 0xebd9f03a = 0xb039bb3d := by decide

example : t 0xb039bb3d = 0x68695433 := by decide

/--
  Extracting the i-th component of eight concatenated
  four-bit strings returns the i-th original string.
-/
theorem Internal.nibble_concat
    (b₇ b₆ b₅ b₄ b₃ b₂ b₁ b₀ : V 4)
    (i : Fin 8) :
    nibble (b₇ ++ b₆ ++ b₅ ++ b₄ ++ b₃ ++ b₂ ++ b₁ ++ b₀) i =
      ![b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇] i := by
  fin_cases i <;>
    simp [nibble, substring] <;>
    bv_decide

/--
  Each four-bit component of t(a) is obtained
  by applying the corresponding substitution πᵢ.
-/
theorem t_substitutes_components (a : V 32) (i : Fin 8) :
    nibble (t a) i = π i (nibble a i) := by
  unfold t
  rw [nibble_concat]
  fin_cases i <;> rfl

-- /--
--   Two 32-bit strings are equal if all their
--   four-bit components are equal.
-- -/
-- private theorem nibble_ext (a b : V 32)
--     (h : ∀ i : Fin 8, nibble a i = nibble b i) :
--     a = b := by
--   have h0 := h 0
--   have h1 := h 1
--   have h2 := h 2
--   have h3 := h 3
--   have h4 := h 4
--   have h5 := h 5
--   have h6 := h 6
--   have h7 := h 7
--   simp only [nibble, substring] at h0 h1 h2 h3 h4 h5 h6 h7
--   bv_decide

/--
  Two 32-bit words with identical four-bit components are equal.
  The proof reconstructs each bit from its nibble, without `bv_decide`
  or native SAT certificate axioms.
-/
theorem Internal.nibble_ext (a b : V 32)
    (h : ∀ i : Fin 8, nibble a i = nibble b i) :
    a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hindex : j / 4 < 8 := by omega
  let i : Fin 8 := ⟨j / 4, hindex⟩
  have hbit := congrArg
    (fun v : V 4 => v.getLsbD (j % 4)) (h i)
  have hmod : j % 4 < 4 := Nat.mod_lt _ (by decide)
  have hdiv : 4 * (j / 4) + j % 4 = j := by omega
  simpa [nibble, substring, i, hmod, hdiv] using hbit

/-- The transformation t is bijective on V₃₂. -/
theorem t_is_bijective : Function.Bijective t := by
  have : Finite (V 32) :=
    Finite.intro ((BitVec.equivFin (m := 32)).toEquiv)
  apply Finite.injective_iff_bijective.mp
  intro a b hab
  apply nibble_ext a b
  intro i
  apply (π_is_bijective i).injective
  calc
    π i (nibble a i) = nibble (t a) i :=
      (t_substitutes_components a i).symm
    _ = nibble (t b) i := by rw [hab]
    _ = π i (nibble b i) :=
      t_substitutes_components b i

noncomputable def tEquiv : V 32 ≃ V 32 :=
  Equiv.ofBijective t t_is_bijective

/--
  g[k] : V₃₂ → V₃₂

  g[k](a) =
    (t(Vec₃₂(Int₃₂(a) [+] Int₃₂(k)))) <<<₁₁
-/
def g (k : V 32) (a : V 32) : V 32 :=
  rot11 (t (Vec_s 32 (add₃₂ (Int_s 32 a) (Int_s 32 k))))

example : g 0x87654321 0xfedcba98 = 0xfdcbc20c := by decide

example : g 0xfdcbc20c 0x87654321 = 0x7e791a4b := by decide

example : g 0x7e791a4b 0xfdcbc20c = 0xc76549ec := by decide

example : g 0xc76549ec 0x7e791a4b = 0x9791c849 := by decide

/--
  For every round key k ∈ V_32, the transformation
  g[k] : V_32 → V_32 is bijective.
-/
theorem g_is_bijective (k : V 32) :
    Function.Bijective (g k) := by
  change Function.Bijective
    (rot11 ∘ t ∘ Vec_s 32 ∘ (fun z : Z2 32 => add₃₂ z (Int_s 32 k)) ∘ Int_s 32)
  exact rot11_is_bijective.comp
    (t_is_bijective.comp
      ((vecEquiv 32).bijective.comp
        ((add₃₂_is_bijective (Int_s 32 k)).comp
          (vecEquiv 32).symm.bijective)))

/-- The bijection g[k] on V_32 for a fixed round key k. -/
noncomputable def gEquiv (k : V 32) : V 32 ≃ V 32 :=
  Equiv.ofBijective (g k) (g_is_bijective k)

/--
  G[k] : V₃₂ × V₃₂ → V₃₂ × V₃₂

  G[k](a₁, a₀) = (a₀, g[k](a₀) ⊕ a₁).
-/
def G (k : V 32) : V 32 × V 32 → V 32 × V 32
  | (a₁, a₀) => (a₀, xor (g k a₀) a₁)

/-- Inverse of the Feistel transformation G[k]. -/
private def G_inv (k : V 32) : V 32 × V 32 → V 32 × V 32
  | (b₁, b₀) => (xor (g k b₁) b₀, b₁)

/-- G_inv[k](G[k](x)) = x. -/
private theorem G_inv_G (k : V 32) (x : V 32 × V 32) :
    G_inv k (G k x) = x := by
  rcases x with ⟨a₁, a₀⟩
  change (xor (g k a₀) (xor (g k a₀) a₁), a₀) = (a₁, a₀)
  rw [xor_cancel_twice]

/-- G[k](G_inv[k](x)) = x. -/
private theorem G_G_inv (k : V 32) (x : V 32 × V 32) :
    G k (G_inv k x) = x := by
  rcases x with ⟨b₁, b₀⟩
  change (b₁, xor (g k b₁) (xor (g k b₁) b₀)) = (b₁, b₀)
  rw [xor_cancel_twice]

/--
  For every fixed round key, G[k] is a bijection on pairs of 32-bit strings.
-/
def GEquiv (k : V 32) :
    (V 32 × V 32) ≃ (V 32 × V 32) where
  toFun := G k
  invFun := G_inv k
  left_inv := G_inv_G k
  right_inv := G_G_inv k

theorem G_is_bijective (k : V 32) : Function.Bijective (G k) :=
  (GEquiv k).bijective

/--
  G*[k] : V₃₂ × V₃₂ → V₆₄

  G*[k](a₁, a₀) = (g[k](a₀) ⊕ a₁) ‖ a₀.
-/
def GStar (k : V 32) : V 32 × V 32 → V 64
  | (a₁, a₀) => (concat ⟨32, xor (g k a₀) a₁⟩ ⟨32, a₀⟩).2

/--
  Splitting G*[k](a₁, a₀) recovers the transformed
  left half and the unchanged right half.
-/
theorem GStar_split (k : V 32) (a₁ a₀ : V 32) :
    split 32 32 (GStar k (a₁, a₀)) = (xor (g k a₀) a₁, a₀) := by
  exact concat_split ⟨32, xor (g k a₀) a₁⟩ ⟨32, a₀⟩

/--
  G*[k] is an equivalence between pairs of
  32-bit strings and 64-bit strings.
-/
def GStarEquiv (k : V 32) :
    (V 32 × V 32) ≃ V 64 :=
  ((GEquiv k).trans (Equiv.prodComm (V 32) (V 32))).trans (splitEquiv 32 32).symm

theorem GStar_equiv_apply (k : V 32) (a₁ a₀ : V 32) : GStarEquiv k (a₁, a₀) = GStar k (a₁, a₀) := by
  rfl

-----------------------------------------------------------------
-- RFC 8891, Section 4.3. Key Schedule
-----------------------------------------------------------------

/--
  Extracts the i-th 32-bit word of the 256-bit master key,
  counting words from left to right, starting at zero.

  K₁ = k₂₅₅ || ... || k₂₂₄
  ...
  K₈ = k₃₁ || ... || k₀
-/
def baseRoundKey (K : V 256) (i : Fin 8) : V 32 :=
  substring K
    (offset := 32 * (7 - i.val))
    (take := 32)
    (by omega)

/--
  Returns round key K_(r+1), where r ∈ Fin 32.

  The first 24 round keys repeat the eight words of
  the master key three times. The last eight use
  these words in reverse order.
-/
def roundKey (K : V 256) (r : Fin 32) : V 32 :=
  let i : Fin 8 :=
    ⟨r.val % 8, Nat.mod_lt _ (by decide)⟩
  if r.val < 24 then
    baseRoundKey K i
  else
    baseRoundKey K ⟨7 - i.val, by omega⟩

/-- K₁, ..., K₈ are the original eight 32-bit words. -/
theorem roundKey_first (K : V 256) (i : Fin 8) :
    roundKey K ⟨i.val, by omega⟩ =
      baseRoundKey K i := by
  fin_cases i <;> rfl

theorem roundKey_repeat8 (K : V 256) (i : Fin 8) :
    roundKey K ⟨i.val + 8, by omega⟩ = roundKey K ⟨i.val, by omega⟩ := by fin_cases i <;> rfl

theorem roundKey_repeat16 (K : V 256) (i : Fin 8) :
    roundKey K ⟨i.val + 16, by omega⟩ = roundKey K ⟨i.val, by omega⟩ := by fin_cases i <;> rfl

theorem roundKey_reverse24 (K : V 256) (i : Fin 8) :
    roundKey K ⟨i.val + 24, by omega⟩ = roundKey K ⟨7 - i.val, by omega⟩ := by fin_cases i <;> rfl

private def testKey : V 256 :=
  0xffeeddccbbaa99887766554433221100f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff#256

/-- RFC 8891, Appendix A.3: master key. -/
private def rfcA3Key : V 256 :=
  0xffeeddccbbaa99887766554433221100f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff#256

/--
  Expected round keys, independently transcribed
  from RFC 8891, Appendix A.3.

  Index 0 corresponds to K₁.
-/
private def rfcA3RoundKeys : Fin 32 → V 32 := ![
  0xffeeddcc, 0xbbaa9988,
  0x77665544, 0x33221100,
  0xf0f1f2f3, 0xf4f5f6f7,
  0xf8f9fafb, 0xfcfdfeff,

  0xffeeddcc, 0xbbaa9988,
  0x77665544, 0x33221100,
  0xf0f1f2f3, 0xf4f5f6f7,
  0xf8f9fafb, 0xfcfdfeff,

  0xffeeddcc, 0xbbaa9988,
  0x77665544, 0x33221100,
  0xf0f1f2f3, 0xf4f5f6f7,
  0xf8f9fafb, 0xfcfdfeff,

  0xfcfdfeff, 0xf8f9fafb,
  0xf4f5f6f7, 0xf0f1f2f3,
  0x33221100, 0x77665544,
  0xbbaa9988, 0xffeeddcc
]

/--
  All 32 generated round keys match RFC 8891,
  Appendix A.3.
-/
example (i : Fin 32) :
    roundKey rfcA3Key i = rfcA3RoundKeys i := by
  fin_cases i <;> decide

-----------------------------------------------------------------
-- RFC 8891, Section 5.1. Encryption
-----------------------------------------------------------------

/--
  E_(K₁,...,K₃₂) : V₆₄ → V₆₄

  E(a) = G*[K₃₂] ∘ G[K₃₁] ∘ ... ∘ G[K₁](a₁, a₀).

  The first 31 rounds apply G, and the final
  round applies GStar.

  Round keys use zero-based indexing in Lean:
  keys 0 = K₁, ..., keys 31 = K₃₂.
-/
def E (keys : Fin 32 → V 32) (a : V 64) : V 64 :=
  let rounds : V 32 × V 32 :=
    Fin.foldl
      31
      (fun state (i : Fin 31) => G (keys i.castSucc) state)
      (split 32 32 a)
  GStar (keys 31) rounds

/--
  Encrypts a 64-bit block using a 256-bit master key,
  deriving the 32 round keys according to RFC 8891 §4.3.
-/
def encrypt (K : V 256) (a : V 64) : V 64 :=
  E (roundKey K) a

/-- Test encryption from RFC 8891, Appendix A.4. -/
example :
    encrypt
      0xffeeddccbbaa99887766554433221100f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff
      0xfedcba9876543210
    = 0x4ee901e5c2d8ca3d := by
  decide +kernel

-----------------------------------------------------------------
-- RFC 8891, Section 5.2. Decryption
-----------------------------------------------------------------

/--
  D_(K₁,...,K₃₂) : V₆₄ → V₆₄

  D(a) = G*[K₁] ∘ G[K₂] ∘ ... ∘ G[K₃₂](a₁, a₀).

  Round keys use zero-based indexing:
  keys 0 = K₁, ..., keys 31 = K₃₂.

  RFC 8891, Section 5.2.
-/
def D (keys : Fin 32 → V 32) (a : V 64) : V 64 :=
  let rounds : V 32 × V 32 :=
    Fin.foldl 31
      (fun state (i : Fin 31) =>
        G (keys ⟨31 - i.val, by omega⟩) state)
      (split 32 32 a)

  GStar (keys 0) rounds

/-- Decryption using a 256-bit master key. -/
def decrypt (K : V 256) (a : V 64) : V 64 :=
  D (roundKey K) a

/-- RFC 8891, Appendix A.5: test decryption. -/
example :
    decrypt
      0xffeeddccbbaa99887766554433221100f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff#256
      0x4ee901e5c2d8ca3d#64
    = 0xfedcba9876543210#64 := by
  decide +kernel

/-- Reverses the order of the 32 round keys. -/
def reverseRoundKeys (keys : Fin 32 → V 32) :
    Fin 32 → V 32 :=
  fun r => keys ⟨31 - r.val, by omega⟩

/--
  Decryption uses the encryption rounds
  with the round keys in reverse order.
-/
theorem D_eq_E_reversed (keys : Fin 32 → V 32) (a : V 64) :
    D keys a = E (reverseRoundKeys keys) a := by
  rfl

/-- RFC 8891, Appendix A.3. -/
private def rfcExampleKey : V 256 :=
  0xffeeddccbbaa99887766554433221100f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff#256

/--
  RFC 8891, Appendix A.4.
  The 33 consecutive 32-bit words occurring in
  the initial state and 31 encryption rounds.
-/
private def rfcEncryptWords : Fin 33 → V 32 := ![
  0xfedcba98, 0x76543210, 0x28da3b14, 0xb14337a5,
  0x633a7c68, 0xea89c02c, 0x11fe726d, 0xad0310a4,
  0x37d97f25, 0x46324615, 0xce995f2a, 0x93c1f449,
  0x4811c7ad, 0xc4b3edca, 0x44ca5ce1, 0xfef51b68,
  0x2098cd86, 0x4f15b0bb, 0xe32805bc, 0xe7116722,
  0x89cadf21, 0xbac8444d, 0x11263a21, 0x625434c3,
  0x8025c0a5, 0xb0d66514, 0x47b1d5f4, 0xc78e6d50,
  0x80251e99, 0x2b96eca6, 0x05ef4401, 0x239a4577,
  0xc2d8ca3d
]

/-- RFC 8891, Appendix A.5. -/
private def rfcDecryptWords : Fin 33 → V 32 := ![
  0x4ee901e5, 0xc2d8ca3d, 0x239a4577, 0x05ef4401,
  0x2b96eca6, 0x80251e99, 0xc78e6d50, 0x47b1d5f4,
  0xb0d66514, 0x8025c0a5, 0x625434c3, 0x11263a21,
  0xbac8444d, 0x89cadf21, 0xe7116722, 0xe32805bc,
  0x4f15b0bb, 0x2098cd86, 0xfef51b68, 0x44ca5ce1,
  0xc4b3edca, 0x4811c7ad, 0x93c1f449, 0xce995f2a,
  0x46324615, 0x37d97f25, 0xad0310a4, 0x11fe726d,
  0xea89c02c, 0x633a7c68, 0xb14337a5, 0x28da3b14,
  0x76543210
]

-----------------------------------------------------------------
-- Proof
-----------------------------------------------------------------

private abbrev State :=
  V 32 × V 32

/-- Concatenate two halves into a 64-bit block. -/
def Internal.pack (p : State) : V 64 :=
  (concat ⟨32, p.1⟩ ⟨32, p.2⟩).2

private theorem split_pack (p : State) : split 32 32 (pack p) = p := by
  rcases p with ⟨a, b⟩
  exact concat_split ⟨32, a⟩ ⟨32, b⟩

private theorem pack_split (a : V 64) : pack (split 32 32 a) = a := by
  change BitVec.extractLsb' 32 32 a ++ BitVec.extractLsb' 0 32 a = a
  exact BitVec.extractLsb'_append_extractLsb'

/--
  A Feistel round, followed by a swap and the same
  Feistel round, equals swapping the original state.
-/
private theorem G_swap_G (k : V 32) (p : State) :
    G k (Prod.swap (G k p)) = Prod.swap p := by
  rcases p with ⟨a₁, a₀⟩
  change
    (a₀, xor (g k a₀) (xor (g k a₀) a₁)) =
      (a₀, a₁)
  rw [xor_cancel_twice]

/-- GStar is G followed by swapping and packing. -/
private theorem GStar_as_pack (k : V 32) (p : State) :
    GStar k p = pack (Prod.swap (G k p)) := by
  rcases p with ⟨a₁, a₀⟩
  rfl

/--
  Forward rounds followed by reverse-order rounds
  cancel, with a swap between the two sequences.
-/
private theorem foldr_foldl_cancel (n : Nat) :
    ∀ (steps : Fin n → State → State) (x : State),
      (∀ i y,
        steps i (Prod.swap (steps i y)) = Prod.swap y) →
      Fin.foldr n (fun i y => steps i y)
        (Prod.swap
          (Fin.foldl n (fun y i => steps i y) x)) =
        Prod.swap x := by
  induction n with
  | zero =>
      intro steps x h
      rfl
  | succ n ih =>
      intro steps x h
      rw [Fin.foldl_succ_last, Fin.foldr_succ_last]
      rw [h (Fin.last n)]
      exact ih (fun i => steps i.castSucc) x
        (by
          intro i y
          exact h i.castSucc y)

/--
  The same cancellation property, expressed
  using foldl in both directions.
-/
private theorem fold_reverse_cancel
    (n : Nat)
    (steps : Fin n → State → State)
    (h : ∀ i y,
      steps i (Prod.swap (steps i y)) = Prod.swap y)
    (x : State) :
    Fin.foldl n
      (fun state i => steps i.rev state)
      (Prod.swap
        (Fin.foldl n (fun state i => steps i state) x)) =
      Prod.swap x := by
  rw [Fin.foldl_rev]
  exact foldr_foldl_cancel n steps x h

/--
  Encryption is 32 consecutive G transformations,
  followed by swapping and concatenation.
-/
theorem Internal.E_as_fold
    (keys : Fin 32 → V 32) (a : V 64) :
    E keys a =
      pack (Prod.swap
        (Fin.foldl 32
          (fun state i => G (keys i) state)
          (split 32 32 a))) := by

  let state31 : State :=
    Fin.foldl 31
      (fun state (i : Fin 31) =>
        G (keys i.castSucc) state)
      (split 32 32 a)

  have h32 :
      Fin.foldl 32
        (fun state (i : Fin 32) => G (keys i) state)
        (split 32 32 a)
      = G (keys 31) state31 := by
    rw [Fin.foldl_succ_last]
    rfl

  calc
    E keys a
        = GStar (keys 31) state31 := by
            rfl

    _ = pack (Prod.swap (G (keys 31) state31)) :=
          GStar_as_pack (keys 31) state31

    _ = pack (Prod.swap
          (Fin.foldl 32
            (fun state i => G (keys i) state)
            (split 32 32 a))) := by
          rw [h32]

private theorem reverseRoundKeys_apply (keys : Fin 32 → V 32) (i : Fin 32) :
    reverseRoundKeys keys i = keys i.rev := by
  unfold reverseRoundKeys
  apply congrArg keys
  apply Fin.ext
  change 31 - i.val = 32 - (i.val + 1)
  omega

private theorem reverseRoundKeys_twice (keys : Fin 32 → V 32) :
    reverseRoundKeys (reverseRoundKeys keys) = keys := by
  funext i
  rw [reverseRoundKeys_apply, reverseRoundKeys_apply]
  exact congrArg keys (Fin.rev_involutive i)

/--
  Encryption with reversed round keys undoes
  encryption with the original round keys.
-/
private theorem E_reverse_E
    (keys : Fin 32 → V 32) (a : V 64) :
    E (reverseRoundKeys keys) (E keys a) = a := by
  rw [E_as_fold (reverseRoundKeys keys) (E keys a)]
  rw [E_as_fold keys a]
  rw [split_pack]
  simp only [reverseRoundKeys_apply]

  have hcancel := fold_reverse_cancel 32
    (fun i => G (keys i))
    (by
      intro i p
      exact G_swap_G (keys i) p)
    (split 32 32 a)

  rw [hcancel]
  simpa only [Prod.swap_swap] using pack_split a

private theorem E_E_reverse (keys : Fin 32 → V 32) (a : V 64) :
    E keys (E (reverseRoundKeys keys) a) = a := by
  have h := E_reverse_E (reverseRoundKeys keys) a
  simpa only [reverseRoundKeys_twice] using h

/--
  Decryption recovers the original plaintext
  for every master key and every 64-bit block.
-/
theorem decrypt_encrypt (K : V 256) (a : V 64) :
    decrypt K (encrypt K a) = a := by
  change D (roundKey K) (E (roundKey K) a) = a
  rw [D_eq_E_reversed]
  exact E_reverse_E (roundKey K) a

/--
  Encryption recovers the original ciphertext
  after decryption.
-/
theorem encrypt_decrypt (K : V 256) (a : V 64) :
    encrypt K (decrypt K a) = a := by
  change E (roundKey K) (D (roundKey K) a) = a
  rw [D_eq_E_reversed]
  exact E_E_reverse (roundKey K) a

/--
  Magma encryption and decryption are
  mutually inverse permutations of V₆₄.
-/
def magmaEquiv (K : V 256) : V 64 ≃ V 64 where
  toFun := encrypt K
  invFun := decrypt K
  left_inv := decrypt_encrypt K
  right_inv := encrypt_decrypt K

-- #print axioms decrypt_encrypt
-- #print axioms encrypt_decrypt
-- #print axioms magmaEquiv
-- #print axioms π'array_is_substitution

------------------
-- Appendix tests
------------------

private def rfcEncryptState (i : Fin 32) : V 32 × V 32 :=
  (rfcEncryptWords i.castSucc, rfcEncryptWords i.succ)

/-- Appendix A.4: initial plaintext halves. -/
example :
    rfcEncryptState 0 =
      split 32 32 0xfedcba9876543210#64 := by
  decide

private def rfcDecryptState (i : Fin 32) : V 32 × V 32 :=
  (rfcDecryptWords i.castSucc, rfcDecryptWords i.succ)

-- Inverse rotation used by the arbitrary-output matrix model.

/-- The proved 11-bit rotation, packaged as an equivalence. -/
noncomputable def Internal.rot11Equiv : V 32 ≃ V 32 :=
  Equiv.ofBijective rot11 rot11_is_bijective

/-- The unique unrotated output difference corresponding to `b`. -/
noncomputable def Internal.unrot11 (b : V 32) : V 32 :=
  rot11Equiv.symm b

/-- Applying the rotation after its inverse returns the output difference. -/
theorem Internal.rot11_unrot11 (b : V 32) : rot11 (unrot11 b) = b := by
  change rot11Equiv (rot11Equiv.symm b) = b
  exact rot11Equiv.apply_symm_apply b

/-- A right rotation by eleven moves each bit eleven places toward lower indices. -/
theorem Internal.rotateRight11_components (b : V 32) (i : Fin 32) :
    component (b.rotateRight 11) i = component b (i + 11) := by
  change (b.rotateRight 11).getLsbD i.val =
    b.getLsbD ((i.val + 11) % 32)
  rw [BitVec.getLsbD_rotateRight_of_lt (by decide : 11 < 32)]
  by_cases h : i.val < 21
  · have h' : i.val < 32 - 11 := by omega
    rw [ite_eq_left h']
    congr 1
    omega
  · have h' : ¬ i.val < 32 - 11 := by omega
    rw [ite_eq_right h']
    have hlt : decide (i.val < 32) = true := by simp [i.isLt]
    simp only [hlt, Bool.true_and]
    congr 1
    omega

/-- Concrete `rotateRight 11` is a right inverse of the RFC's `rot11`.
    The proof is bitwise, with no SAT or native-evaluation axioms. -/
theorem Internal.rot11_rotateRight11 (b : V 32) :
    rot11 (b.rotateRight 11) = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin 32 := (⟨j, hj⟩ : Fin 32) - 11
  have hi : i + 11 = (⟨j, hj⟩ : Fin 32) := by
    dsimp [i]
    simp
  change
    component (rot11 (b.rotateRight 11)) (⟨j, hj⟩ : Fin 32) =
      component b (⟨j, hj⟩ : Fin 32)
  calc
    component (rot11 (b.rotateRight 11)) (⟨j, hj⟩ : Fin 32) =
        component (rot11 (b.rotateRight 11)) (i + 11) := by rw [hi]
    _ = component (b.rotateRight 11) i :=
      rot11_moves_components_up (b.rotateRight 11) i
    _ = component b (i + 11) := rotateRight11_components b i
    _ = component b (⟨j, hj⟩ : Fin 32) := by rw [hi]

/-- The previously defined inverse of `rot11` is the executable right rotation. -/
theorem Internal.unrot11_eq_rotateRight11 (b : V 32) :
    unrot11 b = b.rotateRight 11 := by
  apply rot11_is_bijective.injective
  calc
    rot11 (unrot11 b) = b := rot11_unrot11 b
    _ = rot11 (b.rotateRight 11) := (rot11_rotateRight11 b).symm

end Magma
