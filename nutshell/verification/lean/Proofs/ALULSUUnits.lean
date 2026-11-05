import Proofs.TemporaryPC32
namespace NutShellProofs
open nNutCore
theorem normal_allowed_idu_alulsu (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (allowed : AllowedInstructionFamily (v26223 s i)) :
    v28438 s i = 0 ∨ v28438 s i = 1 := by
  rcases allowed with h | h | h | h | h | h | h | h
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | add => exact Or.inl (idu_immediate_1_add_decode s i normal matched).1
    | slt => exact Or.inl (idu_immediate_1_slt_decode s i normal matched).1
    | sltu => exact Or.inl (idu_immediate_1_sltu_decode s i normal matched).1
    | xor => exact Or.inl (idu_immediate_1_xor_decode s i normal matched).1
    | or => exact Or.inl (idu_immediate_1_or_decode s i normal matched).1
    | and => exact Or.inl (idu_immediate_1_and_decode s i normal matched).1
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | sll => exact Or.inl (idu_shift_1_sll_decode s i normal matched).1
    | srl => exact Or.inl (idu_shift_1_srl_decode s i normal matched).1
    | sra => exact Or.inl (idu_shift_1_sra_decode s i normal matched).1
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | add => exact Or.inl (idu_word_1_add_decode s i normal matched).1
    | sll => exact Or.inl (idu_word_1_sll_decode s i normal matched).1
    | srl => exact Or.inl (idu_word_1_srl_decode s i normal matched).1
    | sra => exact Or.inl (idu_word_1_sra_decode s i normal matched).1
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | lui => exact Or.inl (idu_upper_1_lui_decode s i normal matched).1
    | auipc => exact Or.inl (idu_upper_1_auipc_decode s i normal matched).1
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | add => exact Or.inl (idu_register_alu_1_add_decode s i normal matched).1
    | sub => exact Or.inl (idu_register_alu_1_sub_decode s i normal matched).1
    | slt => exact Or.inl (idu_register_alu_1_slt_decode s i normal matched).1
    | sltu => exact Or.inl (idu_register_alu_1_sltu_decode s i normal matched).1
    | xor => exact Or.inl (idu_register_alu_1_xor_decode s i normal matched).1
    | or => exact Or.inl (idu_register_alu_1_or_decode s i normal matched).1
    | and => exact Or.inl (idu_register_alu_1_and_decode s i normal matched).1
    | sll => exact Or.inl (idu_register_alu_1_sll_decode s i normal matched).1
    | srl => exact Or.inl (idu_register_alu_1_srl_decode s i normal matched).1
    | sra => exact Or.inl (idu_register_alu_1_sra_decode s i normal matched).1
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | beq => exact Or.inl (idu_branch_1_beq_decode s i normal matched).1
    | bne => exact Or.inl (idu_branch_1_bne_decode s i normal matched).1
    | blt => exact Or.inl (idu_branch_1_blt_decode s i normal matched).1
    | bge => exact Or.inl (idu_branch_1_bge_decode s i normal matched).1
    | bltu => exact Or.inl (idu_branch_1_bltu_decode s i normal matched).1
    | bgeu => exact Or.inl (idu_branch_1_bgeu_decode s i normal matched).1
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | jal => exact Or.inl (idu_jump_1_jal_decode s i normal matched).1
    | jalr => exact Or.inl (idu_jump_1_jalr_decode s i normal matched).1
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | lb => exact Or.inr (idu_memory_1_lb_decode s i normal matched).1
    | lh => exact Or.inr (idu_memory_1_lh_decode s i normal matched).1
    | lw => exact Or.inr (idu_memory_1_lw_decode s i normal matched).1
    | ld => exact Or.inr (idu_memory_1_ld_decode s i normal matched).1
    | lbu => exact Or.inr (idu_memory_1_lbu_decode s i normal matched).1
    | lhu => exact Or.inr (idu_memory_1_lhu_decode s i normal matched).1
    | lwu => exact Or.inr (idu_memory_1_lwu_decode s i normal matched).1
    | sb => exact Or.inr (idu_memory_1_sb_decode s i normal matched).1
    | sh => exact Or.inr (idu_memory_1_sh_decode s i normal matched).1
    | sw => exact Or.inr (idu_memory_1_sw_decode s i normal matched).1
    | sd => exact Or.inr (idu_memory_1_sd_decode s i normal matched).1
#print axioms normal_allowed_idu_alulsu
end NutShellProofs
