import Proofs.MulDivCheckedSnapshots

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

/-- The shared nonzero iteration exposes its unsigned quotient and residue
    through monitor snapshots after optional sign correction. -/
theorem nonzero_monitor_result (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 1#7)
    (divisor : s.r7_ndivisor = 0#1 ++ d)
    (initial : s.r8_nremainder = 0#1 ++ ((0#64 ++ a) ++ 0#1))
    (positive : 0 < d.toNat) (unsaved : s.r16_ncontractWasNegated = 0)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    ∃ n, (n = 64 ∨ n = 65) ∧
      v38 (run s inputs n) (inputs n) = 1 ∧
      v232 (run s inputs n) (inputs n) = BitVec.ofNat 64 (a.toNat / d.toNat) ∧
      v233 (run s inputs n) (inputs n) = BitVec.ofNat 64 (a.toNat % d.toNat) := by
  let projected := fun t => coreInputs (inputs t)
  have noReset : ∀ t, t < 64 → (projected t).nreset = 0 := by
    intro t h; exact reset t (by omega)
  have noKill : ∀ t, t < 64 → (projected t).nio_5Fkill = 0 := by
    intro t h; exact alive t (by omega)
  let bits : BitVec 129 := (0#64 ++ a) ++ 0#1
  have bound : HierarchicalRadix.candidate bits < 2 * d.toNat := by
    rw [HierarchicalRadix.candidate_value]
    have value : bits.toNat = 2 * a.toNat := by
      dsimp [bits]
      rw [HierarchicalRadix.append_value, HierarchicalRadix.append_value]
      simp [Nat.mul_comm]
    rw [value]
    have width := a.isLt
    omega
  have core := HierarchicalMulDiv.magnitude_core_result (coreState s) projected a d
    dividing count divisor initial positive noReset noKill
  have active (t : Nat) (h : t < 64) : (run s inputs t).r0_nstate = 3 := by
    have traceFacts := HierarchicalMulDiv.division_prefix (coreState s) projected bits d
      dividing count divisor initial bound noReset noKill t h
    have state := congrArg (fun x => x.r0_nstate) (core_run s inputs t)
    exact state.trans traceFacts.1
  have clear := unsaved_run s inputs 64 unsaved (by
    intro t h; rw [active t h]; decide)
  rw [← core_run s inputs 64] at core
  let negative := s.r4_nneg_5Fout
  let n : Nat := if negative = 1 then 65 else 64
  have result := corrected_monitor_response (run s inputs 64) (inputs 64) (inputs n)
    negative core.1 clear (reset 64 (by omega)) (alive 64 (by omega))
  have trajectory : (if negative = 1 then step (run s inputs 64) (inputs 64)
      else run s inputs 64) = run s inputs n := by
    dsimp [n]; split <;> rfl
  dsimp only at result
  rw [trajectory] at result
  exact ⟨n, by dsimp [n]; split <;> simp, result.1,
    result.2.1.trans core.2.1, result.2.2.trans core.2.2.1⟩

#print axioms nonzero_monitor_result
end HierarchicalMulDivChecked
