import Proofs.ReferenceMemoryException
import Proofs.ReferenceMemoryPC
import Proofs.MemoryBusyRun
namespace NutShellProofs
open nNutCore
theorem reference_memory_exception_alignment (s : State) (i : Inputs) (operation : MemoryOp)
    (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32) :
    v23407 s i = (if BitVec.extractLsb' 0 operation.alignmentBits (v15632 s i + v16164 s i) = 0 then 0 else 1) := by
  cases operation with
  | lb => exact reference_memory_imm_lb_exception_alignment s i commit matched
  | lh => exact reference_memory_imm_lh_exception_alignment s i commit matched
  | lw => exact reference_memory_imm_lw_exception_alignment s i commit matched
  | ld => exact reference_memory_imm_ld_exception_alignment s i commit matched
  | lbu => exact reference_memory_imm_lbu_exception_alignment s i commit matched
  | lhu => exact reference_memory_imm_lhu_exception_alignment s i commit matched
  | lwu => exact reference_memory_imm_lwu_exception_alignment s i commit matched
  | sb => exact reference_memory_imm_sb_exception_alignment s i commit matched
  | sh => exact reference_memory_imm_sh_exception_alignment s i commit matched
  | sw => exact reference_memory_imm_sw_exception_alignment s i commit matched
  | sd => exact reference_memory_imm_sd_exception_alignment s i commit matched

theorem reference_memory_exception_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v23407 (run initial inputs (t + 2)) (inputs (t + 2)) =
      if v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 then 0 else 1 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (28799 : BitVec 32) = operation.encoding.setWidth 32 := by
    have instruction := committed_reference_instruction _ _ _ commit
    change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
      BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
    rw [instruction]
    exact store_match_low32 operation _ matched
  rw [reference_memory_exception_alignment _ _ operation commit low,
    normal_memory_alignment _ _ operation op
      (original_assumptions_lsu_idle_run initial inputs reset environment t),
    memory_address_reference_operands_run initial inputs reset environment t operation commit unit matched registers]
  split <;> simp_all
#print axioms reference_memory_exception_alignment
#print axioms reference_memory_exception_run
theorem aligned_memory_reference_pc_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (aligned : v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (currentReset : (inputs (t + 2)).g0.nreset = 0) :
    (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      v16457 (run initial inputs (t + 2)) (inputs (t + 2)) + 4 := by
  have noException := reference_memory_exception_run initial inputs reset environment t operation commit unit matched registers
  rw [if_pos aligned] at noException
  have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (28799 : BitVec 32) = operation.encoding.setWidth 32 := by
    have instruction := committed_reference_instruction _ _ _ commit
    change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
      BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
    rw [instruction]
    exact store_match_low32 operation _ matched
  exact reference_memory_pc_step _ _ operation currentReset commit low noException
#print axioms aligned_memory_reference_pc_run
end NutShellProofs
