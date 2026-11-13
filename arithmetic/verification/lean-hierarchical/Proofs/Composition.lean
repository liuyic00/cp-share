import Std

namespace HierarchicalComposition

/-- One synchronous transition at each input sample. -/
def run (step : S → I → S) (initial : S) (inputs : Nat → I) : Nat → S
  | 0 => initial
  | n + 1 => step (run step initial inputs n) (inputs n)

/-- A child's input stream is obtained from actual parent states, including
    feedback through other instances; it is not an arbitrary external stream. -/
def childInputs (parentStep : P → I → P) (connect : P → I → J)
    (initial : P) (inputs : Nat → I) (n : Nat) : J :=
  connect (run parentStep initial inputs n) (inputs n)

/-- Lift a checked single-edge state projection to the entire execution. -/
theorem run_projection (parentStep : P → I → P) (childStep : C → J → C)
    (project : P → C) (connect : P → I → J)
    (commutes : ∀ s i, project (parentStep s i) = childStep (project s) (connect s i))
    (initial : P) (inputs : Nat → I) (n : Nat) :
    project (run parentStep initial inputs n) =
      run childStep (project initial) (childInputs parentStep connect initial inputs) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, commutes, ih, childInputs]

/-- The parent must supply a proof of the child's assumptions on its connected
    trajectory. The child's contract then yields its guarantees on that trace. -/
theorem apply_contract
    (assumptions guarantees : C → (Nat → J) → Prop)
    (contract : ∀ initial inputs, assumptions initial inputs → guarantees initial inputs)
    (parentStep : P → I → P) (project : P → C) (connect : P → I → J)
    (initial : P) (inputs : Nat → I)
    (established : assumptions (project initial)
      (childInputs parentStep connect initial inputs)) :
    guarantees (project initial) (childInputs parentStep connect initial inputs) :=
  contract _ _ established

#print axioms run_projection
#print axioms apply_contract
end HierarchicalComposition
