import Proofs.ResetGating

namespace RiscvMiniProofs
open nCoreSoc

-- A reset prefix establishes the hardware state; arbitrary program/data memory
-- and unspecified register initial contents are NOT replaced with zero.
def ResetPrefix (inputs : Nat → Inputs) (cycles : Nat) : Prop :=
  0 < cycles ∧ (∀ t, t < cycles → (inputs t).nreset = 1) ∧
    (∀ t, cycles ≤ t → (inputs t).nreset = 0)

def Environment (initial : State) (inputs : Nat → Inputs) : Prop :=
  ∀ t, assumes (run initial inputs t) (inputs t)

-- Full, unfiltered target. This is a definition of the outstanding obligation,
-- not an axiom or a claimed correctness theorem.
def CorrectAfterReset (cycles : Nat) : Prop :=
  ∀ (initial : State) (inputs : Nat → Inputs),
    ResetPrefix inputs cycles → Environment initial inputs →
      ∀ t, asserts (run initial inputs t) (inputs t)

theorem assertion_count (s : State) (i : Inputs) :
    (eval s i).assertions.length = 45 := by
  simp [eval, assertionChecks, assertionChecks0, assertionChecks1]

def TaskHolds (task : Fin 45) (s : State) (i : Inputs) : Prop :=
  (eval s i).assertions[task.val]'(by rw [assertion_count]; exact task.isLt) = true

-- Completion must supply the original generated conjunction after the prefix.
-- No assumption that an assertion is true is inserted into Environment.
theorem lift_after_reset (cycles : Nat)
    (after : ∀ (initial : State) (inputs : Nat → Inputs),
      ResetPrefix inputs cycles → Environment initial inputs →
        ∀ t, cycles ≤ t → asserts (run initial inputs t) (inputs t)) :
    CorrectAfterReset cycles := by
  intro initial inputs reset env t
  by_cases h : t < cycles
  · exact assertions_during_reset _ _ (reset.2.1 t h)
  · exact after initial inputs reset env t (by omega)

#print axioms lift_after_reset
end RiscvMiniProofs
