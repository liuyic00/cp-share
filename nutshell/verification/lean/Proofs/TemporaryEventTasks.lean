import Proofs.ALUEventTasks
import Proofs.LSUEventTasks
import Proofs.TemporaryRegisterInvariant
namespace NutShellProofs
open nNutCore

/-- Reset disables all five original event assertion gates. -/
theorem reset_event_tasks (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    TaskHolds 43 s i ∧ TaskHolds 44 s i ∧ TaskHolds 45 s i ∧
    TaskHolds 46 s i ∧ TaskHolds 47 s i := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change decide (v31743 s i ≠ 1 ∨ v31740 s i = 1) = true
    simp [v31743, v31742, v14554, v14553, v11455, reset, v24]
  · change decide (v31753 s i ≠ 1 ∨ v31751 s i = 1) = true
    simp [v31753, v31752, v14554, v14553, v11455, reset, v24]
  · change decide (v31766 s i ≠ 1 ∨ v31764 s i = 1) = true
    simp [v31766, v31765, v14554, v14553, v11455, reset, v24]
  · change decide (v31777 s i ≠ 1 ∨ v31775 s i = 1) = true
    simp [v31777, v31776, v14554, v14553, v11455, reset, v24]
  · change decide (v31789 s i ≠ 1 ∨ v31787 s i = 1) = true
    simp [v31789, v31788, v14554, v14553, v11455, reset, v24]

/-- Complete committed instruction coverage under the previously recorded PC32
restriction. PC and register correspondence remain induction obligations. -/
theorem temporary_pc32_committed_event_tasks_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    TaskHolds 43 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 44 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 45 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 46 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 47 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  rcases BitVec.eq_zero_or_eq_one (inputs (t + 2)).g0.nreset with currentReset | currentReset
  · have valid := commit_requires_execute_valid _ _ _ commit
    rcases temporary_pc32_execute_alulsu initial inputs reset environment restriction t valid with alu | lsu
    · exact committed_alu_event_tasks_run initial inputs reset environment t commit alu registers currentReset pc
    · exact committed_lsu_event_tasks_run initial inputs reset environment t commit lsu registers pc
  · exact reset_event_tasks _ _ currentReset
/-- Discharge register correspondence using the existing conditional invariant.
The all-cycle PC premise is still unproved; this is not the full contract. -/
theorem temporary_pc32_committed_events_of_pc (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs)
    (pc : ∀ k, TaskHolds 10 (run initial inputs (k + 2)) (inputs (k + 2)))
    (t : Nat) (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) :
    TaskHolds 43 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 44 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 45 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 46 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 47 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  exact temporary_pc32_committed_event_tasks_run initial inputs reset environment restriction t commit
    (temporary_pc32_registers_run_of_pc initial inputs reset environment restriction pc (t + 1)) (pc t)
#print axioms temporary_pc32_committed_events_of_pc
#print axioms reset_event_tasks
#print axioms temporary_pc32_committed_event_tasks_run
end NutShellProofs
