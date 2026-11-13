import Proofs.MulDivCheckedSnapshots
import Proofs.WidenedDivisionBalance

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem nonzero_magnitude_checks (s : State) (i : Inputs)
    (balance : (v232 s i).toNat * (v220 s i).toNat + (v233 s i).toNat = (v218 s i).toNat)
    (bound : (v233 s i).toNat < (v220 s i).toNat) :
    v282 s i = 1 ∧ v284 s i = 1 := by
  have identity := HierarchicalDivision.widened_balance _ _ _ _ balance
  simp only [v282, v280, v278, v277, v275, v276, v279, v281, v143, v8, v196, v284]
  simp only [identity, bound, if_true]
  exact ⟨trivial, trivial⟩

theorem zero_magnitude_checks (s : State) (i : Inputs)
    (quotient : v232 s i = BitVec.allOnes 64) (remainder : v233 s i = v218 s i) :
    v272 s i = 1 ∧ v274 s i = 1 := by
  simp [v272, v274, v197, quotient, remainder]

/-- Arithmetic obligations for the monitor's saved, uncorrected magnitudes. -/
def MagnitudeInvariant (s : State) : Prop :=
  ∀ i, s.r9_ncontractPending = 1 → v38 s i = 1 → v198 s i = 1 →
    (v220 s i = 0#64 → v232 s i = BitVec.allOnes 64 ∧ v233 s i = v218 s i) ∧
    (v220 s i ≠ 0#64 →
      (v232 s i).toNat * (v220 s i).toNat + (v233 s i).toNat = (v218 s i).toNat ∧
      (v233 s i).toNat < (v220 s i).toNat)

theorem magnitude_checks (s : State) (i : Inputs) (inv : MagnitudeInvariant s) :
    (v273 s i ≠ 1 ∨ v272 s i = 1) ∧ (v273 s i ≠ 1 ∨ v274 s i = 1) ∧
    (v283 s i ≠ 1 ∨ v282 s i = 1) ∧ (v283 s i ≠ 1 ∨ v284 s i = 1) := by
  have zero : s.r9_ncontractPending = 1 → v38 s i = 1 → v198 s i = 1 →
      v220 s i = 0#64 → v272 s i = 1 ∧ v274 s i = 1 := by
    intro pending ready division divisor
    obtain ⟨q, r⟩ := (inv i pending ready division).1 divisor
    exact zero_magnitude_checks s i q r
  have nonzero : s.r9_ncontractPending = 1 → v38 s i = 1 → v198 s i = 1 →
      v220 s i ≠ 0#64 → v282 s i = 1 ∧ v284 s i = 1 := by
    intro pending ready division divisor
    obtain ⟨balance, bound⟩ := (inv i pending ready division).2 divisor
    exact nonzero_magnitude_checks s i balance bound
  simp only [v273, v283, v269, v265, v259, v271, v270, v143, v31]
  bv_decide

end HierarchicalMulDivChecked
