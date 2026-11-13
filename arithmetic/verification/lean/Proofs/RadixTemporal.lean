import Proofs.Radix2Divider

namespace nRadix2Divider
set_option maxRecDepth 8192

/-- All six exported history-based assertions hold after every edge,
including resets and arbitrary changes to request and response pins. -/
theorem temporal_assertions_step (s : State) (i j : Inputs) :
    ((eval (step s i) j).assertions.drop 5).all id = true := by
  simp only [step, eval, List.drop, List.all_cons, List.all_nil, Bool.and_true, id_eq]
  bv_decide

theorem assertion_count (s : State) (i : Inputs) : (eval s i).assertions.length = 11 := by
  rfl

/-- Starting after any edge, all exported temporal assertions hold at every
cycle. No restriction is imposed on the subsequent reset/request trace. -/
theorem temporal_assertions_run (s : State) (first : Inputs) (inputs : Nat → Inputs) (n : Nat) :
    ((eval (run (step s first) inputs n) (inputs n)).assertions.drop 5).all id = true := by
  cases n with
  | zero => exact temporal_assertions_step s first (inputs 0)
  | succ n => exact temporal_assertions_step (run (step s first) inputs n) (inputs n) (inputs (n + 1))

/-- The remaining obligation for the complete exported conjunction consists
exactly of the five arithmetic checks, not the already-proved temporal checks. -/
theorem asserts_after_edge_iff (s : State) (i j : Inputs) :
    asserts (step s i) j ↔ ((eval (step s i) j).assertions.take 5).all id = true := by
  change ((eval (step s i) j).assertions).all id = true ↔ _
  have partition := List.take_append_drop 5 (eval (step s i) j).assertions
  conv => lhs; rw [← partition, List.all_append, temporal_assertions_step, Bool.and_true]

end nRadix2Divider
