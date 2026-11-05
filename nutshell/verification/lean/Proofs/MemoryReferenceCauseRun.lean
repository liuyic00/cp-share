import Proofs.ReferenceMemoryCause
import Proofs.ReferenceMXLEN
import Proofs.ReferenceMemoryPC
import Proofs.MemoryBusyRun
namespace NutShellProofs
open nNutCore
theorem reference_memory_cause_alignment (s : State) (i : Inputs) (operation : MemoryOp)
    (mxlen : s.g47.r1505_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fprivilege_5Fcsr_5FMXLEN = 64)
    (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32) :
    v31763 s i = (if BitVec.extractLsb' 0 operation.alignmentBits (v15632 s i + v16164 s i) = 0 then 0 else (if operation.isLoad then 4 else 6)) := by
  cases operation with
  | lb => exact reference_memory_imm_lb_cause_alignment s i mxlen commit matched
  | lh => exact reference_memory_imm_lh_cause_alignment s i mxlen commit matched
  | lw => exact reference_memory_imm_lw_cause_alignment s i mxlen commit matched
  | ld => exact reference_memory_imm_ld_cause_alignment s i mxlen commit matched
  | lbu => exact reference_memory_imm_lbu_cause_alignment s i mxlen commit matched
  | lhu => exact reference_memory_imm_lhu_cause_alignment s i mxlen commit matched
  | lwu => exact reference_memory_imm_lwu_cause_alignment s i mxlen commit matched
  | sb => exact reference_memory_imm_sb_cause_alignment s i mxlen commit matched
  | sh => exact reference_memory_imm_sh_cause_alignment s i mxlen commit matched
  | sw => exact reference_memory_imm_sw_cause_alignment s i mxlen commit matched
  | sd => exact reference_memory_imm_sd_cause_alignment s i mxlen commit matched

theorem reference_memory_cause_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v31763 (run initial inputs (t + 2)) (inputs (t + 2)) =
      if v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 then 0 else (if operation.isLoad then 4 else 6) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (28799 : BitVec 32) = operation.encoding.setWidth 32 := by
    have instruction := committed_reference_instruction _ _ _ commit
    change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
      BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
    rw [instruction]
    exact store_match_low32 operation _ matched
  rw [reference_memory_cause_alignment _ _ operation (reference_mxlen_run initial inputs reset (t + 1)) commit low,
    normal_memory_alignment _ _ operation op
      (original_assumptions_lsu_idle_run initial inputs reset environment t),
    memory_address_reference_operands_run initial inputs reset environment t operation commit unit matched registers]
  split <;> simp_all
#print axioms reference_memory_cause_alignment
#print axioms reference_memory_cause_run
end NutShellProofs
