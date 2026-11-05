import Proofs.BranchRedirectCapture
namespace NutShellProofs
open nNutCore

theorem alu_redirect_priority (s : State) (i : Inputs) (unit : v3 s i = 0) :
    v25339 s i = 0 ∧ v25354 s i = v13725 s i := by
  have csr : v13181 s i = 0 := by
    simp [v13181, v13180, v13178, v13177, v13176, unit]
  constructor
  · simp [v25339, v27, v26, v7, v5, v4, unit]
  · simp [v25354, v25353, v25349, v25348, v25352, v13454, v13451, v13185, csr]

theorem committed_alu_redirect_target (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (noTrap : v13725 s i = 0) :
    (step s i).g49.r1571_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fcf_5Fredirect_5Ftarget = v12212 s i := by
  obtain ⟨mou, csr⟩ := alu_redirect_priority s i unit
  exact committed_branch_redirect_target s i next commit mou (csr.trans noTrap)

#print axioms alu_redirect_priority
#print axioms committed_alu_redirect_target
theorem branch_alu_redirect_target_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2)))
    (noTrap : v13725 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    (run initial inputs (t + 2)).g49.r1571_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fcf_5Fredirect_5Ftarget =
      BitVec.extractLsb' 0 39
        (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  exact (committed_alu_redirect_target _ _ _ commit unit noTrap).trans
    (branch_next_pc_matches_reference_run initial inputs reset t operation currentReset
      environment commit unit matched aligned pc)


#print axioms branch_alu_redirect_target_matches_reference_run
end NutShellProofs
