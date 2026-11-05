import Proofs.BranchAlignmentAssumption
import Proofs.BranchTargetCorrespondence
import Proofs.ReferenceBranchAlignment
namespace NutShellProofs
open nNutCore

/-- The original environment supplies alignment; PC correctness remains explicit. -/
theorem reference_branch_alignment_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2)))
    (taken : referenceBranchCondition operation (run initial inputs (t + 2)) (inputs (t + 2)) = 1) :
    referenceBranchAlignment operation (run initial inputs (t + 2)) (inputs (t + 2)) = 1 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have noReset := (next_commit_controls _ _ _ commit).1
  have actualTaken := (branch_condition_matches_reference_run initial inputs reset t operation
    commit unit matched aligned).trans taken
  have actualAligned := branch_target_aligned_run initial inputs reset t operation noReset
    environment valid unit matched actualTaken
  have target := branch_target_matches_reference_run initial inputs reset t operation
    currentReset commit unit matched pc
  have low := congrArg (BitVec.extractLsb' 0 2) target
  simp only [low_low _ (by decide : 2 ≤ 39)] at low
  exact reference_branch_alignment operation _ _ (low.symm.trans actualAligned)

#print axioms reference_branch_alignment_run
end NutShellProofs
