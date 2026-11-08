module

public import Magma.RFC8891
public import Magma.Proof.Sbox.ApplyValueLoop
public import Magma.Proof.Decrypt.Block

@[expose] public section

/-!
# RFC 8891 and RustCrypto Tc26

The source-derived Tc26 S-box, 32-round cipher and byte encoding are proved
equivalent to RFC 8891 for all keys and blocks.
Both block methods are proved correct and terminating. Equivalence to the
external `cipher` adapter is not claimed.
-/

namespace Magma.Verification

#check Magma.encrypt

#check Magma.decrypt

#check Magma.Proof.tc26_table_matches_rfc

#check Magma.Proof.tc26_g_if_substitution

#check Magma.Proof.encrypt_inner_step_rfc

#check Magma.Proof.rfc_round_key_of_words

#check Magma.Proof.encrypt_inner_loop_spec

#check Magma.Proof.encrypt_three_loops_spec

#check Magma.Proof.encrypt_reverse_loop_spec

#check Magma.Proof.pure_32_rounds_match_rfc

#check Magma.Proof.to_u32_spec

#check Magma.Proof.encrypt_block_bytes_if_g

#check Magma.Proof.gen_exp_inner_step

#check Magma.Proof.gen_exp_sbox_full

#check Magma.Proof.tc26_gen_exp_correct

#check Magma.Proof.apply_sbox_step_total

#check Magma.Proof.apply_sbox_total

#check Magma.Proof.apply_sbox_step_value

#check Magma.Proof.apply_sbox_loop_value

#check Magma.Proof.expWrite_pointwise

#check Magma.Proof.tc26Expanded_cell

#check Magma.Proof.tc26Expanded_matches_rfc

#check Magma.Proof.tc26_model_matches_rfc

#check Magma.Proof.tc26_apply_sbox_correct

#check Magma.Proof.tc26_g_correct

#check Magma.Proof.encrypt_block_correct

#check Magma.Proof.decrypt_block_correct

end Magma.Verification
