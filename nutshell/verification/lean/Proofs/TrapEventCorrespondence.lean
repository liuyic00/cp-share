import Proofs.FrontendRedirectPC
namespace NutShellProofs
open nNutCore

/-- The actual registered event-valid bit records the trap signal outside reset. -/
theorem captured_event_is_trap (s : State) (i next : Inputs)
    (reset : i.g0.nreset = 0) :
    v31736 (step s i) next = v13725 s i := by
  change v14412 s i = v13725 s i
  simp only [v14412, v13172, v12103, v11455, reset, v24, ↓reduceIte,
    v14411, v14409, v14410, v13725, v13721]
  rcases BitVec.eq_zero_or_eq_one (v13684 s i) with a | a <;>
    rcases BitVec.eq_zero_or_eq_one (v13720 s i) with b | b <;>
      rcases BitVec.eq_zero_or_eq_one (v13724 s i) with c | c <;>
        simp [a, b, c]

/-- Task 43 forces event-valid to agree, including the both-zero case. -/
theorem task43_event_flags (s : State) (i : Inputs) (reset : i.g0.nreset = 0)
    (event : TaskHolds 43 s i) : v31736 s i = v31739 s i := by
  have check : v31743 s i ≠ 1 ∨ v31740 s i = 1 := of_decide_eq_true event
  rcases BitVec.eq_zero_or_eq_one (v31736 s i) with actual | actual <;>
    rcases BitVec.eq_zero_or_eq_one (v31739 s i) with reference | reference <;>
      simp [v31743, v31741, v31742, v14554, v14553, v11455,
        reset, v24, actual, reference, v31740] at check ⊢

theorem task43_no_reference_exception_no_trap (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (reset : next.g0.nreset = 0)
    (event : TaskHolds 43 (step s i) next)
    (noException : v23407 (step s i) next = 0) : v13725 s i = 0 := by
  have priorReset := (next_commit_controls s i next commit).1
  have flags := task43_event_flags (step s i) next reset event
  have reference : v31739 (step s i) next = 0 := by
    simp [v31739, v31738, v31737, v14560, v14559, v14558, commit, noException]
  exact (captured_event_is_trap s i next priorReset).symm.trans (flags.trans reference)

theorem branch_no_trap_from_task43_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2)))
    (event : TaskHolds 43 (run initial inputs (t + 2)) (inputs (t + 2))) :
    v13725 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&&
      operation.mask.setWidth 32 = operation.encoding.setWidth 32 := by
    have instr := committed_reference_instruction
      (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit
    exact (congrArg (fun x => x &&& operation.mask.setWidth 32) instr).trans
      (branch_match_low32 operation _ matched)
  have alignment := reference_branch_alignment_run initial inputs reset t operation
    currentReset environment commit unit matched aligned pc
  have noException := reference_branch_no_exception _ _ operation low alignment
  exact task43_no_reference_exception_no_trap
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2))
    commit currentReset event noException

theorem corrected_branch_frontend_pc_from_task43_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2)))
    (event : TaskHolds 43 (run initial inputs (t + 2)) (inputs (t + 2)))
    (correction : v12218 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    (run initial inputs (t + 3)).g33.r1065_nfrontend_5Fifu_5Fpc =
      BitVec.extractLsb' 0 39
        (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  have noTrap := branch_no_trap_from_task43_run initial inputs reset t operation
    currentReset environment commit unit matched aligned pc event
  exact corrected_branch_frontend_pc_matches_reference_run initial inputs reset t operation
    currentReset environment commit unit matched aligned pc noTrap correction

#print axioms corrected_branch_frontend_pc_from_task43_run
#print axioms branch_no_trap_from_task43_run
#print axioms captured_event_is_trap
#print axioms task43_event_flags
#print axioms task43_no_reference_exception_no_trap
end NutShellProofs
