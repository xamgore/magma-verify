module

public import Magma.RustCrypto.DecryptCipher

@[expose] public section

/-! Total byte-level correctness of the original Aeneas decryption block method. -/

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.RustCrypto

def expectDecryptedBytes (key : Aeneas.Std.Array Std.U32 8#usize)
    (ciphertext : Aeneas.Std.Array Std.U8 8#usize) : List Std.U8 :=
  let st :=
    repeatReverse8Rounds key 3 (runKeyRounds key 0 8 (readWord ciphertext 0, readWord ciphertext 4))
  (st.2.toBEBytes ++ st.1.toBEBytes).map (fun b => (⟨b⟩ : Std.U8))

def rfcDecryptedBytes (key : Aeneas.Std.Array Std.U32 8#usize)
    (ciphertext : Aeneas.Std.Array Std.U8 8#usize) : List Std.U8 :=
  let out := Magma.decrypt (rfcKeyOfWords key) (readWord ciphertext 0 ++ readWord ciphertext 4)
  let halves := Magma.Internal.split 32 32 out
  (halves.1.toBEBytes ++ halves.2.toBEBytes).map (fun b => (⟨b⟩ : Std.U8))

theorem expected_decrypted_bytes_are_rfc (key : Aeneas.Std.Array Std.U32 8#usize)
    (ciphertext : Aeneas.Std.Array Std.U8 8#usize) :
    expectDecryptedBytes key ciphertext = rfcDecryptedBytes key ciphertext := by
  let out :=
    repeatReverse8Rounds key 3 (runKeyRounds key 0 8 (readWord ciphertext 0, readWord ciphertext 4))
  have hs :
    Magma.Internal.split 32 32
        (Magma.decrypt (rfcKeyOfWords key) (readWord ciphertext 0 ++ readWord ciphertext 4)) =
      (out.2, out.1) := by
    rw [← pure_decrypt_32_rounds_match_rfc key (readWord ciphertext 0) (readWord ciphertext 4)]
    exact Magma.concat_split ⟨32, out.2⟩ ⟨32, out.1⟩
  simp only [rfcDecryptedBytes, expectDecryptedBytes]
  rw [hs]

theorem decrypt_block_bytes_if_g (self : RustCryptoTc26.Gost89 RustCryptoTc26.sboxes.Tc26)
    (block : RustCryptoTc26.adapter.InOut (Aeneas.Std.Array Std.U8 8#usize))
    (hg :
      ∀ a k : Std.U32,
        RustCryptoTc26.sboxes.SboxExt.g.default tc26SboxExt a k =
          ok (⟨Magma.g k.bv a.bv⟩ : Std.U32)) :
    RustCryptoTc26.Gost89Tc26.decrypt_block self block ⦃ out =>
      out.output.val = expectDecryptedBytes self.key block.input ⦄ := by
  unfold RustCryptoTc26.Gost89Tc26.decrypt_block
  unfold
    RustCryptoTc26.Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherDecBackendArrayU88.decrypt_block
  simp only [RustCryptoTc26.adapter.InOutABArrayU88.get_in, bind_ok]
  step
  have hlen0 : s.length = 4 := by simpa using s_post1
  step with(to_u32_spec s hlen0)
  step
  have hlen1 : s1.length = 4 := by simpa using s1_post1
  step with(to_u32_spec s1 hlen1)
  have hfirst :=
    decrypt_forward_loop_spec self { start := 0#usize, «end» := 8#usize } i i1 (by decide) hg
  step with hfirst
  subst self1
  have houter := decrypt_three_reverse_loops_spec self i2 i3 hg
  step with houter
  simp only [RustCryptoTc26.adapter.InOut.get_out, bind_ok]
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
    i_post.trans (sliceWord_matches_readWord block.input s hlen0 0 hs0)
  have hi1 : i1.bv = readWord block.input 4 :=
    i1_post.trans (sliceWord_matches_readWord block.input s1 hlen1 4 hs1)
  have hstates :
    (i4.bv, i5.bv) =
      repeatReverse8Rounds self.key 3
        (runKeyRounds self.key 0 8 (readWord block.input 0, readWord block.input 4)) := by
    rw [i4_post, self1_post1, hi0, hi1]
  unfold expectDecryptedBytes
  rw [← hstates]
  simp only [List.map_append]

/-- The original Tc26 block decryption method terminates and returns the RFC plaintext. -/
theorem decrypt_block_correct
    (self : RustCryptoTc26.Gost89 RustCryptoTc26.sboxes.Tc26)
    (block : RustCryptoTc26.adapter.InOut (Aeneas.Std.Array Std.U8 8#usize)) :
    RustCryptoTc26.Gost89Tc26.decrypt_block self block ⦃ out =>
      out.output.val = rfcDecryptedBytes self.key block.input ⦄ := by
  simpa only [expected_decrypted_bytes_are_rfc] using
    (decrypt_block_bytes_if_g self block tc26_g_correct)

end Magma.RustCrypto
