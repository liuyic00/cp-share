import Proofs.IdleEventRun
namespace NutShellProofs
open nNutCore

/-- All original event assertions at every cycle, conditional on the outstanding
PC invariant and the previously documented temporary PC32 restriction. -/
theorem temporary_pc32_events_run_of_pc (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs)
    (pc : ∀ k, TaskHolds 10 (run initial inputs (k + 2)) (inputs (k + 2)))
    (t : Nat) :
    TaskHolds 43 (run initial inputs t) (inputs t) ∧
    TaskHolds 44 (run initial inputs t) (inputs t) ∧
    TaskHolds 45 (run initial inputs t) (inputs t) ∧
    TaskHolds 46 (run initial inputs t) (inputs t) ∧
    TaskHolds 47 (run initial inputs t) (inputs t) := by
  cases t with
  | zero => exact reset_event_tasks _ _ reset
  | succ t =>
    cases t with
    | zero =>
      have actual : v31736 (run initial inputs 1) (inputs 1) = 0 := by
        change v14412 initial (inputs 0) = 0
        simp [v14412, v13172, v12103, v11455, reset, v24]
      have idle : v9 (run initial inputs 1) (inputs 1) = 0 := reset_has_no_next_commit _ _ _ reset
      have reference : v31739 (run initial inputs 1) (inputs 1) = 0 := by
        simp [v31739, v31738, v31737, v14560, v14559, v14558, idle, v24]
      exact event_tasks_when_absent _ _ actual reference
    | succ t =>
      rcases BitVec.eq_zero_or_eq_one (v9 (run initial inputs (t + 2)) (inputs (t + 2))) with idle | commit
      · exact temporary_pc32_idle_event_tasks_run initial inputs reset environment restriction t idle
      · exact temporary_pc32_committed_events_of_pc initial inputs reset environment restriction pc t commit
#print axioms temporary_pc32_events_run_of_pc
end NutShellProofs
