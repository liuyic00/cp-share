import Proofs.BranchRedirectValid
namespace NutShellProofs
open nNutCore

/-- A committed redirect has priority over normal fetch and prediction. -/
theorem frontend_pc_redirect (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1) (redirect : v8 s i = 1) :
    (step s i).g33.r1065_nfrontend_5Fifu_5Fpc =
      s.g49.r1571_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fcf_5Fredirect_5Ftarget := by
  have fire : v14 s i = 1 := by
    simp [v14, v13, v12, v11, v10, commit, redirect]
  change v9675 s i = _
  rcases BitVec.eq_zero_or_eq_one (v9672 s i) with h | h <;>
    simp [v9675, v1, v0, reset, v9674, v9673, fire, h, v2759,
      v2709, v2708, v2707, v2706, v2705]

theorem redirected_branch_frontend_pc_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2)))
    (noTrap : v13725 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (redirect : v8 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) :
    (run initial inputs (t + 3)).g33.r1065_nfrontend_5Fifu_5Fpc =
      BitVec.extractLsb' 0 39
        (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  exact (frontend_pc_redirect _ _ currentReset commit redirect).trans
    (branch_alu_redirect_target_matches_reference_run initial inputs reset t operation
      currentReset environment commit unit matched aligned pc noTrap)

theorem corrected_branch_frontend_pc_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2)))
    (noTrap : v13725 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (correction : v12218 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    (run initial inputs (t + 3)).g33.r1065_nfrontend_5Fifu_5Fpc =
      BitVec.extractLsb' 0 39
        (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  have valid := commit_requires_execute_valid
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit
  obtain ⟨op, _, _, _, _⟩ :=
    (branch_decode_run initial inputs reset t).2 valid operation matched unit
  have captured := committed_branch_redirect_valid
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2))
    operation op commit unit noTrap
  exact redirected_branch_frontend_pc_matches_reference_run initial inputs reset t operation
    currentReset environment commit unit matched aligned pc noTrap (captured.trans correction)

#print axioms corrected_branch_frontend_pc_matches_reference_run
#print axioms frontend_pc_redirect
#print axioms redirected_branch_frontend_pc_matches_reference_run
end NutShellProofs
