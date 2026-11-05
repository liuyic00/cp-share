import Proofs.BranchNextPC
import Proofs.Contract
namespace NutShellProofs
open nNutCore

theorem original_branch_alignment_assumption (s : State) (i : Inputs)
    (environment : assumes s i) (reset : i.g0.nreset = 0)
    (branch : v12182 s i = 1) (taken : v12179 s i = 1) :
    BitVec.extractLsb' 0 2 (v12211 s i) = 0 := by
  have all : (assumptionChecks0 s i).all id = true := environment
  have check : v31810 s i ≠ 1 ∨ v31809 s i = 1 := by
    simp only [assumptionChecks0, List.all_cons, List.all_nil, Bool.and_eq_true,
      Bool.true_and, Bool.and_true, decide_eq_true_eq] at all
    exact of_decide_eq_true all.2.2.1
  have active : v31810 s i = 1 := by simp [v31810, v24, reset]
  have enabled := check.resolve_left (not_not_intro active)
  have mask : v31795 s i = 1 := by
    change v31795 s i &&& v31805 s i = 1 at enabled
    rcases BitVec.eq_zero_or_eq_one (v31795 s i) with z | o
    · simp [z] at enabled
    · exact o
  simpa [v31795, v31791, v31790, branch, taken, v24, v31794, v31792, v31793] using mask

#print axioms original_branch_alignment_assumption
theorem branch_target_aligned_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (taken : v12179 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    BitVec.extractLsb' 0 2 (v12211 (run initial inputs (t + 1)) (inputs (t + 1))) = 0 := by
  have op := ((branch_decode_run initial inputs reset t).2 valid operation matched unit).1
  have branch : v12182 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 := by
    cases operation <;> simp [v12182, v12181, v12141, v28, op, BranchOp.control, v24]
  exact original_branch_alignment_assumption _ _ environment currentReset branch taken

#print axioms branch_target_aligned_run
end NutShellProofs
