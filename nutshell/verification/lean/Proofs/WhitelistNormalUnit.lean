import Proofs.WhitelistCSRControl
namespace NutShellProofs
open nNutCore
theorem normal_allowed_idu_noncsr (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (allowed : AllowedInstructionFamily (v26223 s i)) :
    v28438 s i ≠ 3 := by
  intro csr
  rcases allowed with h | h | h | h | h | h | h | h
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | add =>
      have decoded := (idu_immediate_1_add_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | slt =>
      have decoded := (idu_immediate_1_slt_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | sltu =>
      have decoded := (idu_immediate_1_sltu_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | xor =>
      have decoded := (idu_immediate_1_xor_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | or =>
      have decoded := (idu_immediate_1_or_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | and =>
      have decoded := (idu_immediate_1_and_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | sll =>
      have decoded := (idu_shift_1_sll_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | srl =>
      have decoded := (idu_shift_1_srl_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | sra =>
      have decoded := (idu_shift_1_sra_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | add =>
      have decoded := (idu_word_1_add_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | sll =>
      have decoded := (idu_word_1_sll_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | srl =>
      have decoded := (idu_word_1_srl_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | sra =>
      have decoded := (idu_word_1_sra_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | lui =>
      have decoded := (idu_upper_1_lui_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | auipc =>
      have decoded := (idu_upper_1_auipc_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | add =>
      have decoded := (idu_register_alu_1_add_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | sub =>
      have decoded := (idu_register_alu_1_sub_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | slt =>
      have decoded := (idu_register_alu_1_slt_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | sltu =>
      have decoded := (idu_register_alu_1_sltu_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | xor =>
      have decoded := (idu_register_alu_1_xor_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | or =>
      have decoded := (idu_register_alu_1_or_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | and =>
      have decoded := (idu_register_alu_1_and_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | sll =>
      have decoded := (idu_register_alu_1_sll_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | srl =>
      have decoded := (idu_register_alu_1_srl_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | sra =>
      have decoded := (idu_register_alu_1_sra_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | beq =>
      have decoded := (idu_branch_1_beq_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | bne =>
      have decoded := (idu_branch_1_bne_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | blt =>
      have decoded := (idu_branch_1_blt_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | bge =>
      have decoded := (idu_branch_1_bge_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | bltu =>
      have decoded := (idu_branch_1_bltu_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | bgeu =>
      have decoded := (idu_branch_1_bgeu_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | jal =>
      have decoded := (idu_jump_1_jal_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | jalr =>
      have decoded := (idu_jump_1_jalr_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | lb =>
      have decoded := (idu_memory_1_lb_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | lh =>
      have decoded := (idu_memory_1_lh_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | lw =>
      have decoded := (idu_memory_1_lw_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | ld =>
      have decoded := (idu_memory_1_ld_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | lbu =>
      have decoded := (idu_memory_1_lbu_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | lhu =>
      have decoded := (idu_memory_1_lhu_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | lwu =>
      have decoded := (idu_memory_1_lwu_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | sb =>
      have decoded := (idu_memory_1_sb_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | sh =>
      have decoded := (idu_memory_1_sh_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | sw =>
      have decoded := (idu_memory_1_sw_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
    | sd =>
      have decoded := (idu_memory_1_sd_decode s i normal matched).1
      rw [csr] at decoded
      contradiction
#print axioms normal_allowed_idu_noncsr
end NutShellProofs
