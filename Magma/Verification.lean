module

public import Magma.RFC8891
public import Magma.Proof.Sbox.ApplyValueLoop
public import Magma.Proof.Common.KeyInit
public import Magma.Proof.Decrypt.Block

@[expose] public section

/-!
# RFC 8891 correspondence for the extracted Magma cipher

The extracted substitution table, Feistel rounds, key schedule and block
encoding agree with RFC 8891 for every key and input block.
Both block methods are proved correct and terminating. Equivalence to the
external `cipher` adapter is not claimed.
-/

namespace Magma.Verification

#check Magma.encrypt

#check Magma.decrypt

#check Magma.Proof.rust_table_matches_rfc

#check Magma.Proof.round_function_matches_rfc_of_substitution

#check Magma.Proof.encrypt_inner_loop_step_matches_rfc

#check Magma.Proof.key_init_correct

#check Magma.Proof.round_key_matches_rust_schedule

#check Magma.Proof.encrypt_inner_loop_correct

#check Magma.Proof.encrypt_repeated_forward_loops_correct

#check Magma.Proof.encrypt_reverse_loop_correct

#check Magma.Proof.encrypt_round_schedule_matches_rfc

#check Magma.Proof.to_u32_reads_big_endian_bytes

#check Magma.Proof.encrypt_block_matches_expected_bytes_of_g_correct

#check Magma.Proof.expanded_sbox_generation_inner_step

#check Magma.Proof.expanded_sbox_generation_correct

#check Magma.Proof.rust_expanded_sbox_generation_correct

#check Magma.Proof.apply_sbox_step_succeeds

#check Magma.Proof.apply_sbox_terminates

#check Magma.Proof.apply_sbox_step_value

#check Magma.Proof.apply_sbox_loop_matches_accumulator

#check Magma.Proof.expWrite_pointwise

#check Magma.Proof.rust_expanded_table_cell_correct

#check Magma.Proof.rust_expanded_sbox_matches_rfc

#check Magma.Proof.rust_model_matches_rfc

#check Magma.Proof.rust_apply_sbox_correct

#check Magma.Proof.rust_g_correct

#check Magma.Proof.encrypt_block_correct

#check Magma.Proof.decrypt_block_correct

end Magma.Verification
