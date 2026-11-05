import Proofs.AluRedirectPriority
import Proofs.LSUExceptions
namespace NutShellProofs
open nNutCore

/-- Any actual trap overrides the normal redirect path. -/
theorem trap_redirect (s : State) (i : Inputs) (trap : v13725 s i = 1) :
    v25387 s i = 1 := by
  have csr : v25354 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v25348 s i) with h | h <;>
      rcases BitVec.eq_zero_or_eq_one (v25352 s i) with k | k <;>
        simp [v25354, v25353, v25349, trap, h, k]
  by_cases mou : v25339 s i = 1
  · simp only [v25387, v25386, mou, ↓reduceIte]
  · simp only [v25387, v25386, mou, ↓reduceIte, v25385, csr]

theorem committed_trap_flushes_next (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (trap : v13725 s i = 1) :
    v23 (step s i) next = 1 := by
  have redirectNext : v8 (step s i) next = 1 := by
    change v25388 s i = 1
    rw [v25388, if_pos (commit_requires_capture s i next commit), trap_redirect s i trap]
  simp [v23, v22, v21, v20, v19, v18, v17, v14, v13, v12, v11,
    v10, commit, redirectNext, v15]

theorem next_unflushed_has_no_trap (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (flush : v23 (step s i) next = 0) :
    v13725 s i = 0 := by
  rcases BitVec.eq_zero_or_eq_one (v13725 s i) with zero | one
  · exact zero
  · have bad := committed_trap_flushes_next s i next commit one
    rw [flush] at bad
    contradiction

#print axioms trap_redirect
#print axioms committed_trap_flushes_next
#print axioms next_unflushed_has_no_trap

/-- A following consecutive commit rules out a trap in the earlier instruction. -/
theorem consecutive_commits_no_trap (s : State) (i next after : Inputs)
    (commit : v9 (step s i) next = 1)
    (following : v9 (step (step s i) next) after = 1) :
    v13725 s i = 0 := by
  exact next_unflushed_has_no_trap s i next commit
    (commit_requires_unflushed (step s i) next after following)

theorem consecutive_branch_redirect_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2)))
    (following : v9 (run initial inputs (t + 3)) (inputs (t + 3)) = 1) :
    (run initial inputs (t + 2)).g49.r1571_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fcf_5Fredirect_5Ftarget =
      BitVec.extractLsb' 0 39
        (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  have noTrap := consecutive_commits_no_trap
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2))
    (inputs (t + 3)) commit following
  exact branch_alu_redirect_target_matches_reference_run initial inputs reset t operation
    currentReset environment commit unit matched aligned pc noTrap

#print axioms consecutive_commits_no_trap
#print axioms consecutive_branch_redirect_matches_reference_run
end NutShellProofs
