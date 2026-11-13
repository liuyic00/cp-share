import Proofs.MulDivCheckedSnapshots
import Proofs.MulDivSignedZero

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

/-- The zero-divisor iteration records all-one quotient and the original
    dividend, even when the response subsequently needs sign correction. -/
theorem zero_monitor_result (s : State) (inputs : Nat → Inputs) (a : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = 0#65) (initial : s.r8_nremainder = 0#66 ++ a)
    (unsaved : s.r16_ncontractWasNegated = 0)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    ∃ n, (n = 65 ∨ n = 66) ∧
      v38 (run s inputs n) (inputs n) = 1 ∧
      v232 (run s inputs n) (inputs n) = BitVec.allOnes 64 ∧
      v233 (run s inputs n) (inputs n) = a := by
  let projected := fun t => coreInputs (inputs t)
  have noReset : ∀ t, t < 65 → (projected t).nreset = 0 := by
    intro t h; exact reset t (by omega)
  have noKill : ∀ t, t < 65 → (projected t).nio_5Fkill = 0 := by
    intro t h; exact alive t (by omega)
  have core := HierarchicalMulDiv.zero_magnitude_result (coreState s) projected a
    dividing count divisor initial noReset noKill
  have active (t : Nat) (h : t < 65) : (run s inputs t).r0_nstate = 3 := by
    have traceFacts := HierarchicalMulDiv.zero_prefix (coreState s) projected a
      dividing count divisor initial noReset noKill t (by omega)
    have state := congrArg (fun x => x.r0_nstate) (core_run s inputs t)
    exact state.trans traceFacts.1
  have clear := unsaved_run s inputs 65 unsaved (by
    intro t h; rw [active t h]; decide)
  rw [← core_run s inputs 65] at core
  let negative := HierarchicalMulDiv.zeroCorrection (coreState s)
  let n : Nat := if negative = 1 then 66 else 65
  have result := corrected_monitor_response (run s inputs 65) (inputs 65) (inputs n)
    negative core.1 clear (reset 65 (by omega)) (alive 65 (by omega))
  have trajectory : (if negative = 1 then step (run s inputs 65) (inputs 65)
      else run s inputs 65) = run s inputs n := by
    dsimp [n]; split <;> rfl
  dsimp only at result
  rw [trajectory] at result
  exact ⟨n, by dsimp [n]; split <;> simp, result.1,
    result.2.1.trans core.2.1, result.2.2.trans core.2.2.1⟩

#print axioms zero_monitor_result
end HierarchicalMulDivChecked
