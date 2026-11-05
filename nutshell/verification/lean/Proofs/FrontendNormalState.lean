import Proofs.FrontendOffsetAlignment
namespace NutShellProofs
open nNutCore

def FrontendBufferNormal (s : State) : Prop :=
  s.g33.r1072_nfrontend_5Fibf_5Fstate = 0 ∨ s.g33.r1072_nfrontend_5Fibf_5Fstate = 1

theorem frontend_normal_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    FrontendBufferNormal (step s i) := by
  left
  change v10128 s i = 0
  simp [v10128, v9714, v0, reset, v4079]

/-- Aligned offsets cannot request either special cross-boundary state. -/
theorem frontend_aligned_crossing_signals_zero (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 (v9735 s i) = 0) :
    v9803 s i = 0 ∧ v9810 s i = 0 ∧ v10109 s i = 0 ∧ v10110 s i = 0 := by
  have notSix : v9735 s i ≠ BitVec.ofNat 3 6 := by
    intro six
    rw [six] at aligned
    contradiction
  simp [v9803, v9810, v10109, v10110, v9797, v9782, v9736,
    v9809, v9806, v9804, v97, notSix]

theorem frontend_normal_step_without_crossing (s : State) (i : Inputs)
    (normal : FrontendBufferNormal s)
    (a : v9803 s i = 0) (b : v9810 s i = 0)
    (c : v10109 s i = 0) (d : v10110 s i = 0) :
    FrontendBufferNormal (step s i) := by
  rcases normal with state | state
  all_goals
    change v10128 s i = 0 ∨ v10128 s i = 1
    simp [v10128, v10127, v10126, v10125, v10124, v10123,
      v10108, v10107, v10106, v10105, v10118, v10117, v10116, v10115,
      v9718, v10090, v10092, v10093, state, a, b, c, d, v4079, v10089,
      v9721, v2750]
    all_goals repeat' first | (split <;> simp_all only [↓reduceIte, or_true, true_or]) | (first | exact Or.inl rfl | exact Or.inr rfl)

  all_goals
    by_cases h0 : v9714 s i = 1 <;> by_cases h1 : v9717 s i = 1 <;>
      by_cases h2 : v10112 s i = 1 <;> by_cases h3 : v10114 s i = 1 <;> simp_all

theorem frontend_normal_step (s : State) (i : Inputs)
    (normal : FrontendBufferNormal s)
    (aligned : BitVec.extractLsb' 0 2 (v9735 s i) = 0) :
    FrontendBufferNormal (step s i) := by
  obtain ⟨a,b,c,d⟩ := frontend_aligned_crossing_signals_zero s i aligned
  exact frontend_normal_step_without_crossing s i normal a b c d

theorem frontend_normal_step_empty (s : State) (i : Inputs)
    (normal : FrontendBufferNormal s) (empty : v9802 s i = 0) :
    FrontendBufferNormal (step s i) := by
  apply frontend_normal_step_without_crossing s i normal
  · simp [v9803, empty]
  · simp [v9810, empty]
  · simp [v10109, empty]
  · simp [v10110, empty]

/-- Normal states exclude the halfword-restart branch in the offset update. -/
theorem frontend_normal_not_special (s : State) (i : Inputs)
    (normal : FrontendBufferNormal s) : v10092 s i = 0 := by
  rcases normal with state | state <;> simp [v10092, v9721, state]
#print axioms frontend_normal_reset
#print axioms frontend_aligned_crossing_signals_zero
#print axioms frontend_normal_step
#print axioms frontend_normal_not_special
end NutShellProofs
