import Proofs.MulDivCheckedZeroMagnitude
import Proofs.MulDivCheckedNonzeroMagnitude
import Proofs.MulDivCheckedTrace
import Proofs.MulDivNormalized

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

def magnitudeQuotient (a d : BitVec 64) : BitVec 64 :=
  if d = 0#64 then BitVec.allOnes 64 else BitVec.ofNat 64 (a.toNat / d.toNat)

def magnitudeResidue (a d : BitVec 64) : BitVec 64 :=
  if d = 0#64 then a else BitVec.ofNat 64 (a.toNat % d.toNat)

theorem magnitude_balance (a d : BitVec 64) (nonzero : d ≠ 0#64) :
    (magnitudeQuotient a d).toNat * d.toNat + (magnitudeResidue a d).toNat = a.toNat ∧
    (magnitudeResidue a d).toNat < d.toNat := by
  have positive : 0 < d.toNat := by
    have h : d.toNat ≠ 0 := by
      intro h; exact nonzero (BitVec.eq_of_toNat_eq h)
    omega
  have quotientBound : a.toNat / d.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt
  have residueBound : a.toNat % d.toNat < 2 ^ 64 :=
    Nat.lt_trans (Nat.mod_lt _ positive) d.isLt
  simp only [magnitudeQuotient, magnitudeResidue, nonzero, if_false,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt quotientBound, Nat.mod_eq_of_lt residueBound]
  exact ⟨by simpa [Nat.mul_comm] using Nat.div_add_mod a.toNat d.toNat,
    Nat.mod_lt _ positive⟩

/-- Both divisor cases use the same count-zero interface and expose the same
    magnitude specification, independently of final sign correction. -/
theorem normalized_monitor_result (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (initial : s.r8_nremainder = 0#66 ++ a)
    (unsaved : s.r16_ncontractWasNegated = 0)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    ∃ n, (n = 65 ∨ n = 66) ∧
      v38 (run s inputs n) (inputs n) = 1 ∧
      v232 (run s inputs n) (inputs n) = magnitudeQuotient a d ∧
      v233 (run s inputs n) (inputs n) = magnitudeResidue a d := by
  by_cases zero : d = 0#64
  · have result := zero_monitor_result s inputs a dividing count
      (by simpa [zero] using divisor) initial unsaved reset alive
    simpa [magnitudeQuotient, magnitudeResidue, zero] using result
  · have leading := HierarchicalMulDiv.normalized_leading (coreState s) (coreInputs (inputs 0))
      a d dividing count divisor initial zero (reset 0 (by omega)) (alive 0 (by omega))
    rw [← core_step] at leading
    have positive : 0 < d.toNat := by
      have nonzero : d.toNat ≠ 0 := by
        intro h; exact zero (BitVec.eq_of_toNat_eq h)
      omega
    have clear := unsaved_before_correction s (inputs 0) unsaved (by rw [dividing]; decide)
    obtain ⟨n, time, valid, quotient, residue⟩ := nonzero_monitor_result (step s (inputs 0))
      (fun t => inputs (1 + t)) a d leading.1 leading.2.1 leading.2.2.1
      leading.2.2.2.1 positive clear
      (by intro t h; exact reset (1 + t) (by omega))
      (by intro t h; exact alive (1 + t) (by omega))
    refine ⟨1 + n, by omega, ?_, ?_, ?_⟩
    · rw [run_offset]; exact valid
    · rw [run_offset]; simpa [magnitudeQuotient, zero] using quotient
    · rw [run_offset]; simpa [magnitudeResidue, zero] using residue

#print axioms normalized_monitor_result
end HierarchicalMulDivChecked
