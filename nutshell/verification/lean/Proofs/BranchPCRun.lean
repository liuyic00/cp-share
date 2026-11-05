import Proofs.BranchAlignmentCorrespondence
import Proofs.ReferenceBranchPCUpdate
namespace NutShellProofs
open nNutCore

theorem reference_branch_pc_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      if v12179 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 then
        referenceBranchTarget operation (run initial inputs (t + 2)) (inputs (t + 2))
      else v16457 (run initial inputs (t + 2)) (inputs (t + 2)) + 4 := by
  have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&&
      operation.mask.setWidth 32 = operation.encoding.setWidth 32 := by
    have instr := committed_reference_instruction
      (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit
    exact (congrArg (fun x => x &&& operation.mask.setWidth 32) instr).trans
      (branch_match_low32 operation _ matched)
  have alignment := reference_branch_alignment_run initial inputs reset t operation
    currentReset environment commit unit matched aligned pc
  have result := reference_branch_pc_update _ _ operation currentReset commit low alignment
  have condition := branch_condition_matches_reference_run initial inputs reset t operation
    commit unit matched aligned
  rw [← condition] at result
  exact result

#print axioms reference_branch_pc_run
theorem branch_next_pc_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    v12212 (run initial inputs (t + 1)) (inputs (t + 1)) =
      BitVec.extractLsb' 0 39
        (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  have refNext := reference_branch_pc_run initial inputs reset t operation currentReset
    environment commit unit matched aligned pc
  rw [refNext]
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((branch_decode_run initial inputs reset t).2 valid operation matched unit).1
  have branch : v12182 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 := by
    cases operation <;> simp [v12182, v12181, v12141, v28, op, BranchOp.control, v24]
  have target := branch_target_matches_reference_run initial inputs reset t operation currentReset commit unit matched pc
  have seq := branch_sequential_pc (run initial inputs (t + 1)) (inputs (t + 1)) operation matched
  have pcs := committed_operand_pc_from_task10 _ _ _ currentReset commit pc
  have seqRef := congrArg (fun x : BitVec 64 => BitVec.extractLsb' 0 39 (x + 4)) pcs
  simp only [low_add _ _ (by decide : 39 ≤ 64), extendOperandPC,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 39),
    BitVec.extractLsb'_eq_self] at seqRef
  rw [v12212, v12190, v12189, branch]
  by_cases taken : v12179 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
  · simp only [taken, v24]
    simpa using target
  · have zero : v12179 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
      rcases BitVec.eq_zero_or_eq_one (v12179 (run initial inputs (t + 1)) (inputs (t + 1))) with z | o
      · exact z
      · exact False.elim (taken o)
    simp only [zero, v24]
    simpa [low_add _ _ (by decide : 39 ≤ 64)] using seq.trans seqRef

#print axioms branch_next_pc_matches_reference_run
end NutShellProofs
