import Proofs.LSUIdleInvariant
import Proofs.FrontendRedirectPC
namespace NutShellProofs
open nNutCore

theorem branch_recovery_from_original_assumptions_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2)))
    (correction : v12218 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    (run initial inputs (t + 3)).g33.r1065_nfrontend_5Fifu_5Fpc =
      BitVec.extractLsb' 0 39
        (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  have valid := commit_requires_execute_valid
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit
  have noTrap := branch_no_trap_run initial inputs reset environment t operation valid unit matched
  exact corrected_branch_frontend_pc_matches_reference_run initial inputs reset t operation
    currentReset (environment (t + 1)) commit unit matched aligned pc noTrap correction

#print axioms branch_recovery_from_original_assumptions_run
end NutShellProofs
