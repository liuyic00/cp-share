import Proofs.ReferenceMemoryRedirect
import Proofs.ReferencePCUpdate
namespace NutShellProofs
open nNutCore
theorem reference_memory_pc_step (s : State) (i : Inputs) (operation : MemoryOp)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (noException : v23407 s i = 0) :
    (step s i).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc = v16457 s i + 4 := by
  cases operation with
  | lb =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_memory_imm_lb_not_v14595 s i matched)
      (reference_memory_imm_lb_not_v14601 s i matched),
      reference_memory_imm_lb_no_redirect s i matched]
    rfl
  | lh =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_memory_imm_lh_not_v14595 s i matched)
      (reference_memory_imm_lh_not_v14601 s i matched),
      reference_memory_imm_lh_no_redirect s i matched]
    rfl
  | lw =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_memory_imm_lw_not_v14595 s i matched)
      (reference_memory_imm_lw_not_v14601 s i matched),
      reference_memory_imm_lw_no_redirect s i matched]
    rfl
  | ld =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_memory_imm_ld_not_v14595 s i matched)
      (reference_memory_imm_ld_not_v14601 s i matched),
      reference_memory_imm_ld_no_redirect s i matched]
    rfl
  | lbu =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_memory_imm_lbu_not_v14595 s i matched)
      (reference_memory_imm_lbu_not_v14601 s i matched),
      reference_memory_imm_lbu_no_redirect s i matched]
    rfl
  | lhu =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_memory_imm_lhu_not_v14595 s i matched)
      (reference_memory_imm_lhu_not_v14601 s i matched),
      reference_memory_imm_lhu_no_redirect s i matched]
    rfl
  | lwu =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_memory_imm_lwu_not_v14595 s i matched)
      (reference_memory_imm_lwu_not_v14601 s i matched),
      reference_memory_imm_lwu_no_redirect s i matched]
    rfl
  | sb =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_memory_imm_sb_not_v14595 s i matched)
      (reference_memory_imm_sb_not_v14601 s i matched),
      reference_memory_imm_sb_no_redirect s i matched]
    rfl
  | sh =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_memory_imm_sh_not_v14595 s i matched)
      (reference_memory_imm_sh_not_v14601 s i matched),
      reference_memory_imm_sh_no_redirect s i matched]
    rfl
  | sw =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_memory_imm_sw_not_v14595 s i matched)
      (reference_memory_imm_sw_not_v14601 s i matched),
      reference_memory_imm_sw_no_redirect s i matched]
    rfl
  | sd =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_memory_imm_sd_not_v14595 s i matched)
      (reference_memory_imm_sd_not_v14601 s i matched),
      reference_memory_imm_sd_no_redirect s i matched]
    rfl
#print axioms reference_memory_pc_step
end NutShellProofs
