import Proofs.TrapEventCorrespondence
namespace NutShellProofs
open nNutCore

/-- A DUT trap absent from the reference is a failure of the original event assertion. -/
theorem committed_unmatched_trap_fails_task43 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (reset : next.g0.nreset = 0)
    (trap : v13725 s i = 1) (reference : v23407 (step s i) next = 0) :
    ¬ TaskHolds 43 (step s i) next := by
  intro event
  have zero := task43_no_reference_exception_no_trap s i next commit reset event reference
  rw [trap] at zero
  contradiction

/-- State-level form used to interpret concrete candidate traces, without a reachability claim. -/
theorem unmatched_event_fails_task43 (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (actual : v31736 s i = 1)
    (reference : v31739 s i = 0) : ¬ TaskHolds 43 s i := by
  intro event
  have eq := task43_event_flags s i reset event
  rw [actual, reference] at eq
  contradiction
#print axioms committed_unmatched_trap_fails_task43
#print axioms unmatched_event_fails_task43
end NutShellProofs
