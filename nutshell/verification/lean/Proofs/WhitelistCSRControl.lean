import Proofs.MemoryDispatch
namespace NutShellProofs
open nNutCore
def NoCSRWriteDecoded (instr : BitVec 64) (unit : BitVec 3) (op : BitVec 7) : Prop :=
  AllowedInstructionFamily instr → unit = 3 → op = 0
theorem idu_no_csr_write_0 (s : State) (i : Inputs) :
    NoCSRWriteDecoded (v26210 s i) (v28254 s i) (v28643 s i) := by
  intro allowed csr
  rcases BitVec.eq_zero_or_eq_one (v28077 s i) with normal | exceptional
  · have normal : v26384 s i = 0 := normal
    rcases allowed with h | h | h | h | h | h | h | h
    · obtain ⟨operation, matched⟩ := h
      cases operation with
      | add =>
        have decoded := (idu_immediate_0_add_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | slt =>
        have decoded := (idu_immediate_0_slt_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | sltu =>
        have decoded := (idu_immediate_0_sltu_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | xor =>
        have decoded := (idu_immediate_0_xor_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | or =>
        have decoded := (idu_immediate_0_or_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | and =>
        have decoded := (idu_immediate_0_and_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
    · obtain ⟨operation, matched⟩ := h
      cases operation with
      | sll =>
        have decoded := (idu_shift_0_sll_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | srl =>
        have decoded := (idu_shift_0_srl_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | sra =>
        have decoded := (idu_shift_0_sra_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
    · obtain ⟨operation, matched⟩ := h
      cases operation with
      | add =>
        have decoded := (idu_word_0_add_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | sll =>
        have decoded := (idu_word_0_sll_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | srl =>
        have decoded := (idu_word_0_srl_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | sra =>
        have decoded := (idu_word_0_sra_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
    · obtain ⟨operation, matched⟩ := h
      cases operation with
      | lui =>
        have decoded := (idu_upper_0_lui_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | auipc =>
        have decoded := (idu_upper_0_auipc_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
    · obtain ⟨operation, matched⟩ := h
      cases operation with
      | add =>
        have decoded := (idu_register_alu_0_add_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | sub =>
        have decoded := (idu_register_alu_0_sub_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | slt =>
        have decoded := (idu_register_alu_0_slt_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | sltu =>
        have decoded := (idu_register_alu_0_sltu_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | xor =>
        have decoded := (idu_register_alu_0_xor_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | or =>
        have decoded := (idu_register_alu_0_or_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | and =>
        have decoded := (idu_register_alu_0_and_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | sll =>
        have decoded := (idu_register_alu_0_sll_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | srl =>
        have decoded := (idu_register_alu_0_srl_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | sra =>
        have decoded := (idu_register_alu_0_sra_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
    · obtain ⟨operation, matched⟩ := h
      cases operation with
      | beq =>
        have decoded := (idu_branch_0_beq_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | bne =>
        have decoded := (idu_branch_0_bne_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | blt =>
        have decoded := (idu_branch_0_blt_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | bge =>
        have decoded := (idu_branch_0_bge_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | bltu =>
        have decoded := (idu_branch_0_bltu_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | bgeu =>
        have decoded := (idu_branch_0_bgeu_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
    · obtain ⟨operation, matched⟩ := h
      cases operation with
      | jal =>
        have decoded := (idu_jump_0_jal_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | jalr =>
        have decoded := (idu_jump_0_jalr_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
    · obtain ⟨operation, matched⟩ := h
      cases operation with
      | lb =>
        have decoded := (idu_memory_0_lb_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | lh =>
        have decoded := (idu_memory_0_lh_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | lw =>
        have decoded := (idu_memory_0_lw_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | ld =>
        have decoded := (idu_memory_0_ld_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | lbu =>
        have decoded := (idu_memory_0_lbu_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | lhu =>
        have decoded := (idu_memory_0_lhu_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | lwu =>
        have decoded := (idu_memory_0_lwu_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | sb =>
        have decoded := (idu_memory_0_sb_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | sh =>
        have decoded := (idu_memory_0_sh_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | sw =>
        have decoded := (idu_memory_0_sw_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
      | sd =>
        have decoded := (idu_memory_0_sd_decode s i normal matched).1
        rw [csr] at decoded
        contradiction
  · have exceptionalOp : v28454 s i = 1 := exceptional
    simp [v28640, v28641, v28642, v28643, v28452, v28451, csr, v28615, exceptionalOp, v28455]
#print axioms idu_no_csr_write_0
theorem idu_no_csr_write_1 (s : State) (i : Inputs) :
    NoCSRWriteDecoded (v26223 s i) (v28438 s i) (v28836 s i) := by
  intro allowed csr
  rcases BitVec.eq_zero_or_eq_one (v28261 s i) with normal | exceptional
  · have normal : v26911 s i = 0 := normal
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
  · have exceptionalOp : v28649 s i = 1 := exceptional
    simp [v28833, v28834, v28835, v28836, v28647, v28646, csr, v28808, exceptionalOp, v28650]
#print axioms idu_no_csr_write_1
end NutShellProofs
