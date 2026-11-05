import Proofs.BranchPCRun
namespace NutShellProofs
open nNutCore

/-- Actual redirect target capture; priority overrides remain explicit. -/
theorem committed_branch_redirect_target (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (noMou : v25339 s i = 0) (noCSR : v25354 s i = 0) :
    (step s i).g49.r1571_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fcf_5Fredirect_5Ftarget = v12212 s i := by
  change v25374 s i = _
  simp only [v25374, commit_requires_capture s i next commit, v25373, v25372,
    noMou, v25371, noCSR, v12213, ↓reduceIte]
  rfl

#print axioms committed_branch_redirect_target
theorem branch_redirect_target_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2)))
    (noMou : v25339 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (noCSR : v25354 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    (run initial inputs (t + 2)).g49.r1571_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fcf_5Fredirect_5Ftarget =
      BitVec.extractLsb' 0 39
        (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  exact (committed_branch_redirect_target _ _ _ commit noMou noCSR).trans
    (branch_next_pc_matches_reference_run initial inputs reset t operation currentReset
      environment commit unit matched aligned pc)

#print axioms branch_redirect_target_matches_reference_run
end NutShellProofs
