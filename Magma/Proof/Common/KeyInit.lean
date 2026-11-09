module

public import Magma.Proof.Common.Ranges
public import Magma.Proof.Common.Bytes

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.Proof

def keyWord (key : Aeneas.Std.Array Std.U8 32#usize) (i : Nat) : BitVec 32 :=
  (BitVec.fromBEBytes ((key.val.slice (i * 4) (i * 4 + 4)).map Std.U8.bv)).setWidth 32

private lemma slice_word_eq_key_word (key : Aeneas.Std.Array Std.U8 32#usize) (i : Nat)
    (s : Slice Std.U8) (hlen : s.length = 4) (hs : s.val = key.val.slice (i * 4) (i * 4 + 4)) :
    sliceWord s hlen = keyWord key i := by
  unfold sliceWord keyWord
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_cast, BitVec.toNat_setWidth]
  rw [hs]
  have hl : (key.val.slice (i * 4) (i * 4 + 4)).length = 4 := by
    rw [← hs]
    simpa [Slice.length] using hlen
  have hbits : 8 * ((key.val.slice (i * 4) (i * 4 + 4)).map Std.U8.bv).length = 32 := by simp [hl]
  have hb := BitVec.isLt (BitVec.fromBEBytes ((key.val.slice (i * 4) (i * 4 + 4)).map Std.U8.bv))
  have hb32 :
    (BitVec.fromBEBytes ((key.val.slice (i * 4) (i * 4 + 4)).map Std.U8.bv)).toNat < 2 ^ 32 := by
    simpa only [hbits] using hb
  exact (Nat.mod_eq_of_lt hb32).symm

private def keyPrefix (key : Aeneas.Std.Array Std.U8 32#usize)
    (words : Aeneas.Std.Array Std.U32 8#usize) (n : Nat) : Prop :=
  ∀ j : Fin 8, j.val < n → (words.val[j.val]!).bv = keyWord key j.val

private lemma key_init_loop_spec (key : Aeneas.Std.Array Std.U8 32#usize)
    (words : Aeneas.Std.Array Std.U32 8#usize) (iter : core.ops.range.Range Std.Usize)
    (hbound : iter.start.val ≤ iter.end.val ∧ iter.end.val = 8)
    (hprefix : keyPrefix key words iter.start.val) :
    Magma.Rust.Gost89.Insts.MagmaAdapterKeyInit.new_loop iter key words ⦃ out =>
      keyPrefix key out 8 ⦄ := by
  unfold Magma.Rust.Gost89.Insts.MagmaAdapterKeyInit.new_loop
  apply
    loop.spec_decr_nat (measure := fun s => 8 - s.1.start.val) (inv := fun s =>
      s.1.end.val = 8 ∧ s.1.start.val ≤ 8 ∧ keyPrefix key s.2 s.1.start.val)
  · intro s hs
    rcases s with ⟨it, w⟩
    rcases hs with ⟨hend, hle, hpre⟩
    dsimp only [Prod.fst, Prod.snd] at *
    by_cases hstep : it.start.val < it.end.val
    · have hnext := usize_range_next_some it hstep
      unfold Magma.Rust.Gost89.Insts.MagmaAdapterKeyInit.new_loop.body
      step with hnext
      subst o
      step*
      have hlen : chunk.length = 4 := by omega
      step with(to_u32_reads_big_endian_bytes chunk hlen)
      have hi : it.start.val < w.length := by
        simp; omega
      step with(Array.update_spec w it.start word hi)
      have hslice : chunk.val = key.val.slice (it.start.val * 4) (it.start.val * 4 + 4) := by
        have he : «end».val = it.start.val * 4 + 4 := by omega
        simpa only [Array.val_to_slice, start_post, he] using chunk_post
      have hword : word.bv = keyWord key it.start.val :=
        word_post.trans (slice_word_eq_key_word key it.start.val chunk hlen hslice)
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [o_post2] using hend
      · omega
      · intro j hj
        change (a.val[j.val]!).bv = keyWord key j.val
        rw [a_post]
        by_cases hji : j.val = it.start.val
        · have hset : ((w.set it.start word).val[j.val]!).bv = word.bv := by
            simpa only [Array.getElem!_Nat_eq] using
              congrArg (fun x : Std.U32 => x.bv)
                (Array.getElem!_Nat_set_eq w it.start j.val word ⟨hji.symm, by simp⟩)
          rw [hset]
          simpa [hji] using hword
        · have hprev : j.val < it.start.val := by omega
          have hvalue := hpre j hprev
          have hset : ((w.set it.start word).val[j.val]!).bv = (w.val[j.val]!).bv := by
            simpa only [Array.getElem!_Nat_eq] using
              congrArg (fun x : Std.U32 => x.bv)
                (Array.getElem!_Nat_set_ne w it.start j.val word (Ne.symm hji))
          rw [hset]
          exact hvalue
      · omega
    · have hnone := usize_range_next_none it (by omega)
      unfold Magma.Rust.Gost89.Insts.MagmaAdapterKeyInit.new_loop.body
      step with hnone
      subst o
      simpa only [WP.spec_ok] using
        (show keyPrefix key w 8 from by
          have h8 : it.start.val = 8 := by omega
          simpa [h8] using hpre)
  · refine ⟨hbound.2, ?_, hprefix⟩
    change iter.start.val ≤ 8
    omega

/-- The translated Rust key initializer produces the big-endian word at every position. -/
lemma key_init_words_correct (key : Aeneas.Std.Array Std.U8 32#usize) :
    Magma.Rust.adapter.verify_key_init key ⦃ out =>
      ∀ j : Fin 8, (out.key.val[j.val]!).bv = keyWord key j.val ⦄ := by
  unfold Magma.Rust.adapter.verify_key_init
  unfold Magma.Rust.Gost89.Insts.MagmaAdapterKeyInit.new
  have hstart : keyPrefix key (Array.repeat 8#usize 0#u32) 0 := by
    intro j hj
    omega
  have hloop := key_init_loop_spec key (Array.repeat 8#usize 0#u32)
      { start := 0#usize, «end» := 8#usize } (by decide) hstart
  step with hloop
  intro j
  exact out_post j j.isLt

/-- Pack the 32 input bytes into the 256-bit RFC key in network byte order. -/
def rfcKeyOfBytes (key : Aeneas.Std.Array Std.U8 32#usize) : BitVec 256 :=
  pack8Words (fun i => keyWord key i.val)

/-- The extracted key constructor preserves the full 256-bit RFC key. -/
theorem key_init_correct (key : Aeneas.Std.Array Std.U8 32#usize) :
    Magma.Rust.adapter.verify_key_init key ⦃ out =>
      rfcKeyOfWords out.key = rfcKeyOfBytes key ⦄ := by
  apply WP.spec_mono (key_init_words_correct key)
  intro out hwords
  simpa [rfcKeyOfWords, rfcKeyOfBytes] using
    congrArg pack8Words (funext (fun j => hwords j))

end Magma.Proof
