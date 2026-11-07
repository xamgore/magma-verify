module

public import Magma.RFC8891
public import Magma.RustCrypto
public import Magma.RustCrypto.SboxApplyValueLoop
public import Magma.RustCrypto.DecryptBlock

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

#check Magma.RustCrypto.tc26_table_matches_rfc

#check Magma.RustCrypto.tc26_g_if_substitution

#check Magma.RustCrypto.encrypt_inner_step_rfc

#check Magma.RustCrypto.rfc_round_key_of_words

#check Magma.RustCrypto.encrypt_inner_loop_spec

#check Magma.RustCrypto.encrypt_three_loops_spec

#check Magma.RustCrypto.encrypt_reverse_loop_spec

#check Magma.RustCrypto.pure_32_rounds_match_rfc

#check Magma.RustCrypto.to_u32_spec

#check Magma.RustCrypto.encrypt_block_bytes_if_g

#check Magma.RustCrypto.gen_exp_inner_step

#check Magma.RustCrypto.gen_exp_sbox_full

#check Magma.RustCrypto.tc26_gen_exp_correct

#check Magma.RustCrypto.apply_sbox_step_total

#check Magma.RustCrypto.apply_sbox_total

#check Magma.RustCrypto.apply_sbox_step_value

#check Magma.RustCrypto.apply_sbox_loop_value

#check Magma.RustCrypto.expWrite_pointwise

#check Magma.RustCrypto.tc26Expanded_cell

#check Magma.RustCrypto.tc26Expanded_matches_rfc

#check Magma.RustCrypto.tc26_model_matches_rfc

#check Magma.RustCrypto.tc26_apply_sbox_correct

#check Magma.RustCrypto.tc26_g_correct

#check Magma.RustCrypto.encrypt_block_correct

#check Magma.RustCrypto.decrypt_block_correct

end Magma.Verification
