import Proofs.Contract

namespace NutShellProofs
open nNutCore

def ReferenceZero (s : State) : Prop :=
  s.g44.r1439_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F0 = 0

theorem reference_zero_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    ReferenceZero (step s i) := by
  change v14565 s i = 0
  simp [v14565, v14555, v14554, v14553, v11455, v14557, v14556,
    v11814, v4051, reset]

theorem reference_zero_step (s : State) (i : Inputs) (zero : ReferenceZero s) :
    ReferenceZero (step s i) := by
  change v14565 s i = 0
  have hz : v14562 s i = 0 := zero
  simp [v14565, v14557, v14556, v11814, v4051, v14564, v14563,
    v14561, hz]

theorem reference_zero_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    ReferenceZero (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact reference_zero_reset initial (inputs 0) reset
  | succ t ih => exact reference_zero_step _ _ ih

theorem reference_zero_after_reset (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (t : Nat) (positive : 0 < t) :
    ReferenceZero (run initial inputs t) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  exact reference_zero_run initial inputs (reset.2.1 0 reset.1) k

#print axioms reference_zero_after_reset
end NutShellProofs
