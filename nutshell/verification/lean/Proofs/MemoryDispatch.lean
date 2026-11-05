import Proofs.JumpDecode
import Proofs.MemoryPipeline
namespace NutShellProofs
open nNutCore

def MemoryDispatch (instr : BitVec 64) (unit : BitVec 3) : Prop :=
  AllowedInstructionFamily instr → unit = 1 → ∃ op, IsMemory op instr

theorem idu_memory_dispatch_0 (s : State) (i : Inputs) :
    MemoryDispatch (v26210 s i) (v28254 s i) := by
  intro allowed lsu
  have inactive : v28077 s i = 0 := by
    rcases BitVec.eq_zero_or_eq_one (v28077 s i) with zero | one
    · exact zero
    · simp [v28254, one, v28078] at lsu
  have normal : v26384 s i = 0 := inactive
  rcases allowed with h | h | h | h | h | h | h | h
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | add =>
      have alu := (idu_immediate_0_add_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | slt =>
      have alu := (idu_immediate_0_slt_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sltu =>
      have alu := (idu_immediate_0_sltu_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | xor =>
      have alu := (idu_immediate_0_xor_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | or =>
      have alu := (idu_immediate_0_or_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | and =>
      have alu := (idu_immediate_0_and_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | sll =>
      have alu := (idu_shift_0_sll_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | srl =>
      have alu := (idu_shift_0_srl_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sra =>
      have alu := (idu_shift_0_sra_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | add =>
      have alu := (idu_word_0_add_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sll =>
      have alu := (idu_word_0_sll_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | srl =>
      have alu := (idu_word_0_srl_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sra =>
      have alu := (idu_word_0_sra_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | lui =>
      have alu := (idu_upper_0_lui_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | auipc =>
      have alu := (idu_upper_0_auipc_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | add =>
      have alu := (idu_register_alu_0_add_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sub =>
      have alu := (idu_register_alu_0_sub_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | slt =>
      have alu := (idu_register_alu_0_slt_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sltu =>
      have alu := (idu_register_alu_0_sltu_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | xor =>
      have alu := (idu_register_alu_0_xor_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | or =>
      have alu := (idu_register_alu_0_or_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | and =>
      have alu := (idu_register_alu_0_and_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sll =>
      have alu := (idu_register_alu_0_sll_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | srl =>
      have alu := (idu_register_alu_0_srl_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sra =>
      have alu := (idu_register_alu_0_sra_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | beq =>
      have alu := (idu_branch_0_beq_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | bne =>
      have alu := (idu_branch_0_bne_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | blt =>
      have alu := (idu_branch_0_blt_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | bge =>
      have alu := (idu_branch_0_bge_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | bltu =>
      have alu := (idu_branch_0_bltu_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | bgeu =>
      have alu := (idu_branch_0_bgeu_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | jal =>
      have alu := (idu_jump_0_jal_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | jalr =>
      have alu := (idu_jump_0_jalr_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
  · exact h
#print axioms idu_memory_dispatch_0
theorem idu_memory_dispatch_1 (s : State) (i : Inputs) :
    MemoryDispatch (v26223 s i) (v28438 s i) := by
  intro allowed lsu
  have inactive : v28261 s i = 0 := by
    rcases BitVec.eq_zero_or_eq_one (v28261 s i) with zero | one
    · exact zero
    · simp [v28438, one, v28262] at lsu
  have normal : v26911 s i = 0 := inactive
  rcases allowed with h | h | h | h | h | h | h | h
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | add =>
      have alu := (idu_immediate_1_add_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | slt =>
      have alu := (idu_immediate_1_slt_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sltu =>
      have alu := (idu_immediate_1_sltu_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | xor =>
      have alu := (idu_immediate_1_xor_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | or =>
      have alu := (idu_immediate_1_or_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | and =>
      have alu := (idu_immediate_1_and_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | sll =>
      have alu := (idu_shift_1_sll_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | srl =>
      have alu := (idu_shift_1_srl_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sra =>
      have alu := (idu_shift_1_sra_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | add =>
      have alu := (idu_word_1_add_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sll =>
      have alu := (idu_word_1_sll_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | srl =>
      have alu := (idu_word_1_srl_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sra =>
      have alu := (idu_word_1_sra_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | lui =>
      have alu := (idu_upper_1_lui_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | auipc =>
      have alu := (idu_upper_1_auipc_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | add =>
      have alu := (idu_register_alu_1_add_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sub =>
      have alu := (idu_register_alu_1_sub_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | slt =>
      have alu := (idu_register_alu_1_slt_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sltu =>
      have alu := (idu_register_alu_1_sltu_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | xor =>
      have alu := (idu_register_alu_1_xor_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | or =>
      have alu := (idu_register_alu_1_or_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | and =>
      have alu := (idu_register_alu_1_and_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sll =>
      have alu := (idu_register_alu_1_sll_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | srl =>
      have alu := (idu_register_alu_1_srl_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | sra =>
      have alu := (idu_register_alu_1_sra_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | beq =>
      have alu := (idu_branch_1_beq_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | bne =>
      have alu := (idu_branch_1_bne_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | blt =>
      have alu := (idu_branch_1_blt_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | bge =>
      have alu := (idu_branch_1_bge_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | bltu =>
      have alu := (idu_branch_1_bltu_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | bgeu =>
      have alu := (idu_branch_1_bgeu_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
  · obtain ⟨operation, matched⟩ := h
    cases operation with
    | jal =>
      have alu := (idu_jump_1_jal_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
    | jalr =>
      have alu := (idu_jump_1_jalr_decode s i normal matched).1
      rw [lsu] at alu
      contradiction
  · exact h
#print axioms idu_memory_dispatch_1
end NutShellProofs
