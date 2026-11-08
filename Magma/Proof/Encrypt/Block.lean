module

public import Magma.Proof.Common.Bytes

@[expose] public section

/-!
# Byte-exact Aeneas `encrypt_block` refinement

The source-derived function reads eight bytes into two big-endian words,
executes all 32 *original loop bodies*, then writes the swapped halves back
to the output through `copy_from_slice`. Every step is proved to succeed.

The internal lemma uses the g contract, discharged by SboxFinal.lean.
-/

open Aeneas Aeneas.Std Result

namespace Magma.Proof

/-- Unambiguous big-endian word from four bytes of the input. -/
def readWord (b : Aeneas.Std.Array Std.U8 8#usize) (start : Nat) : BitVec 32 :=
  (BitVec.fromBEBytes ((b.val.slice start (start+4)).map Std.U8.bv)).setWidth 32

def expectEncryptedBytes (key : Aeneas.Std.Array Std.U32 8#usize)
    (plain : Aeneas.Std.Array Std.U8 8#usize) : List Std.U8 :=
  let st := runReverseRounds key 0 8 (repeat8Rounds key 3 (readWord plain 0, readWord plain 4))
  (st.2.toBEBytes ++ st.1.toBEBytes).map (fun b => (⟨b⟩ : Std.U8))

lemma setSlice0_four (b x : List α) (hb : b.length = 8) (hx : x.length = 4) :
    b.setSlice! 0 x = x ++ b.drop 4 := by simp [List.setSlice!, hb, hx]

lemma setSlice4_four (b x y : List α) (hb : b.length = 8) (hx : x.length = 4) (hy : y.length = 4) :
    (b.setSlice! 0 x).setSlice! 4 y = x ++ y := by
  rw [setSlice0_four b x hb hx]
  simp [List.setSlice!, hb, hx, hy]

lemma slice_word_equals_block_word (b : Aeneas.Std.Array Std.U8 8#usize) (s : Slice Std.U8)
    (h4 : s.length = 4) (start : Nat) (hs : s.val = b.val.slice start (start + 4)) :
    sliceWord s h4 = readWord b start := by
  unfold sliceWord readWord
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_cast, BitVec.toNat_setWidth]
  rw [← hs]
  have hwidth : 8 * (s.val.map Std.U8.bv).length = 32 := by
    simp [Slice.length] at h4
    simp [h4]
  have hlt : (BitVec.fromBEBytes (s.val.map Std.U8.bv)).toNat < 2 ^ 32 := by
    rw [← hwidth]
    exact BitVec.isLt _
  rw [Nat.mod_eq_of_lt hlt]

theorem encrypt_block_matches_expected_bytes_of_g_correct
    (self : Magma.Rust.Gost89 Magma.Rust.sboxes.Tc26)
    (block : Magma.Rust.adapter.InOut (Aeneas.Std.Array Std.U8 8#usize))
    (hg :
      ∀ a k : Std.U32,
        Magma.Rust.sboxes.SboxExt.g.default rustSboxExt a k = ok (⟨Magma.g k.bv a.bv⟩ : Std.U32)) :
    Magma.Proof.Crate.encrypt_block self block ⦃ out =>
      out.output.val = expectEncryptedBytes self.key block.input ⦄ := by
  unfold Magma.Proof.Crate.encrypt_block
  unfold Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block
  simp only [Magma.Rust.adapter.InOutABArrayU88.get_in, bind_ok]
  step
  have hlen0 : s.length = 4 := by simpa using s_post1
  step with(to_u32_reads_big_endian_bytes s hlen0)
  step
  have hlen1 : s1.length = 4 := by simpa using s1_post1
  step with(to_u32_reads_big_endian_bytes s1 hlen1)
  have houter := encrypt_repeated_forward_loops_correct self i i1 hg
  step with houter
  subst self1
  simp only [core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default, bind_ok]
  have hreverse :=
    encrypt_reverse_loop_correct self ⟨{ start := 0#usize, «end» := 8#usize }⟩ i2 i3 (by decide) hg
  step with hreverse
  simp only [Magma.Rust.adapter.InOut.get_out, bind_ok]
  step*
  have hs4 : s4.val = a.val := by rw [s4_post, s3_post, Array.val_to_slice]
  have hs7 : s7.val = a1.val := by rw [s7_post, s6_post, Array.val_to_slice]
  have hblocklen : block.output.val.length = 8 := by simp
  have hlenA : a.val.length = 4 := by simp
  have hlenA1 : a1.val.length = 4 := by simp
  have hbytes : (index_mut_back1 s7).val = a.val ++ a1.val := by
    rw [s5_post2 s7, s2_post2 s4, hs4, hs7]
    exact setSlice4_four block.output.val a.val a1.val hblocklen hlenA hlenA1
  rw [hbytes, a_post, a1_post]
  have hs0 : s.val = block.input.val.slice 0 4 := by simpa only [Array.val_to_slice] using s_post
  have hs1 : s1.val = block.input.val.slice 4 8 := by simpa only [Array.val_to_slice] using s1_post
  have hi0 : i.bv = readWord block.input 0 :=
    i_post.trans (slice_word_equals_block_word block.input s hlen0 0 hs0)
  have hi1 : i1.bv = readWord block.input 4 :=
    i1_post.trans (slice_word_equals_block_word block.input s1 hlen1 4 hs1)
  have hstates :
    (i4.bv, i5.bv) =
      runReverseRounds self.key 0 8
        (repeat8Rounds self.key 3 (readWord block.input 0, readWord block.input 4)) := by
    rw [i4_post, self1_post1, hi0, hi1]
  unfold expectEncryptedBytes
  rw [← hstates]
  simp only [List.map_append]

end Magma.Proof
