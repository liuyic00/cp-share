import Proofs.LSUIdleInvariant
import Proofs.TrapEventCorrespondence
namespace NutShellProofs
open nNutCore

theorem event_tasks_when_absent (s : State) (i : Inputs)
    (actual : v31736 s i = 0) (reference : v31739 s i = 0) :
    TaskHolds 43 s i ∧ TaskHolds 44 s i ∧ TaskHolds 45 s i ∧ TaskHolds 46 s i ∧ TaskHolds 47 s i := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change decide (v31743 s i ≠ 1 ∨ v31740 s i = 1) = true
    simp [v31743, v31741, actual, reference]
  · change decide (v31753 s i ≠ 1 ∨ v31751 s i = 1) = true
    simp [v31753, v31741, actual, reference]
  · change decide (v31766 s i ≠ 1 ∨ v31764 s i = 1) = true
    simp [v31766, v31741, actual, reference]
  · change decide (v31777 s i ≠ 1 ∨ v31775 s i = 1) = true
    simp [v31777, v31741, actual, reference]
  · change decide (v31789 s i ≠ 1 ∨ v31787 s i = 1) = true
    simp [v31789, v31741, actual, reference]

theorem branch_event_flags_zero_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    v31736 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 ∧
    v31739 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
  have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&&
      operation.mask.setWidth 32 = operation.encoding.setWidth 32 := by
    have instr := committed_reference_instruction
      (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit
    exact (congrArg (fun x => x &&& operation.mask.setWidth 32) instr).trans
      (branch_match_low32 operation _ matched)
  have alignment := reference_branch_alignment_run initial inputs reset t operation
    currentReset (environment (t + 1)) commit unit matched aligned pc
  have noException := reference_branch_no_exception _ _ operation low alignment
  have valid := commit_requires_execute_valid
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit
  have noTrap := branch_no_trap_run initial inputs reset environment t operation valid unit matched
  have priorReset := (next_commit_controls
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit).1
  have actual : v31736 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 :=
    (captured_event_is_trap _ _ _ priorReset).trans noTrap
  have reference : v31739 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
    simp [v31739, v31738, v31737, v14560, v14559, v14558, commit, noException]
  exact ⟨actual, reference⟩

theorem branch_event_task43_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    TaskHolds 43 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  obtain ⟨actual, reference⟩ := branch_event_flags_zero_run initial inputs reset t operation currentReset environment commit unit matched aligned pc
  exact (event_tasks_when_absent _ _ actual reference).1

theorem branch_event_tasks_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    TaskHolds 43 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 44 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 45 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 46 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 47 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  obtain ⟨actual, reference⟩ := branch_event_flags_zero_run initial inputs reset t operation currentReset environment commit unit matched aligned pc
  exact event_tasks_when_absent _ _ actual reference

#print axioms branch_event_flags_zero_run
#print axioms branch_event_tasks_run
#print axioms branch_event_task43_run
end NutShellProofs
