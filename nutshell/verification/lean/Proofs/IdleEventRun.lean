import Proofs.IdleExceptionCompletion
import Proofs.TemporaryEventTasks
namespace NutShellProofs
open nNutCore

/-- No commit means no captured DUT exception event on reachable ALU/LSU runs. -/
theorem temporary_pc32_idle_actual_event_zero (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (idle : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 0) :
    v31736 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
  rcases BitVec.eq_zero_or_eq_one (inputs (t + 1)).g0.nreset with priorReset | priorReset
  · have captured := captured_event_is_trap (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) priorReset
    change v31736 (run initial inputs (t + 2)) (inputs (t + 2)) = _ at captured
    rw [captured]
    rcases BitVec.eq_zero_or_eq_one (v6 (run initial inputs (t + 1)) (inputs (t + 1))) with valid | valid
    · simp [v13725, v13724, v13723, valid]
    · rcases temporary_pc32_execute_alulsu initial inputs reset environment restriction t valid with alu | lsu
      · have inactive := idle_next_alu_inactive _ _ (inputs (t + 2)) priorReset alu idle
        simp [v13725, inactive]
      · rcases BitVec.eq_zero_or_eq_one (v23 (run initial inputs (t + 1)) (inputs (t + 1))) with flush | flush
        · obtain ⟨operation, matched, _⟩ := original_assumptions_lsu_memory_run initial inputs reset environment t valid lsu
          have illegal := (memory_legal_run initial inputs reset t).2 valid operation matched lsu
          have faults := idle_next_lsu_no_fault _ _ (inputs (t + 2)) priorReset flush valid lsu idle
          exact memory_no_trap_remaining_sources_run initial inputs reset t valid lsu illegal faults.1 faults.2
        · simp [v13725, v13724, v13723, v13722, flush, v24]
  · change v14412 (run initial inputs (t + 1)) (inputs (t + 1)) = 0
    simp [v14412, v13172, v12103, v11455, priorReset, v24]

/-- Original event assertions on all idle cycles from cycle two. -/
theorem temporary_pc32_idle_event_tasks_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (idle : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 0) :
    TaskHolds 43 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 44 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 45 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 46 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 47 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have actual := temporary_pc32_idle_actual_event_zero initial inputs reset environment restriction t idle
  have reference : v31739 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
    simp [v31739, v31738, v31737, v14560, v14559, v14558, idle, v24]
  exact event_tasks_when_absent _ _ actual reference
#print axioms temporary_pc32_idle_actual_event_zero
#print axioms temporary_pc32_idle_event_tasks_run
end NutShellProofs
