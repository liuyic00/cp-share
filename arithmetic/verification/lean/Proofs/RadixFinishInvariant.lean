import Proofs.RadixArithmeticChecks

namespace nRadix2Divider
set_option maxRecDepth 8192

/-- Captured magnitudes and the final packed quotient/remainder, before sign
correction or word formatting. -/
def MagnitudeCorrect (s : State) : Prop :=
  if s.r1_ndivBy0Reg = 1 then
    s.r2_nshiftReg.extractLsb' 0 64 = 18446744073709551615 ∧
    s.r2_nshiftReg.extractLsb' 65 64 = s.r6_naValx2Reg.extractLsb' 1 64
  else
    s.r5_nbReg.toNat > 0 ∧
    (s.r2_nshiftReg.extractLsb' 0 64).toNat =
      (s.r6_naValx2Reg.extractLsb' 1 64).toNat / s.r5_nbReg.toNat ∧
    (s.r2_nshiftReg.extractLsb' 65 64).toNat =
      (s.r6_naValx2Reg.extractLsb' 1 64).toNat % s.r5_nbReg.toNat

def FinishInvariant (s : State) : Prop := s.r0_nstate = 4 → MagnitudeCorrect s

theorem magnitude_correct_checks (s : State) (i : Inputs) (correct : MagnitudeCorrect s) :
    ((eval s i).assertions.take 5).all id = true := by
  unfold MagnitudeCorrect at correct
  split at correct
  · rename_i flag
    exact arithmetic_checks_zero s i flag correct.1 correct.2
  · rename_i flag
    have zero : s.r1_ndivBy0Reg = 0 := by bv_decide
    exact arithmetic_checks_nonzero s i zero correct.1 correct.2.1 correct.2.2

theorem finish_invariant_asserts (s : State) (previous i : Inputs)
    (correct : FinishInvariant (step s previous)) : asserts (step s previous) i := by
  rw [asserts_after_edge_iff]
  by_cases finish : (step s previous).r0_nstate = 4
  · exact magnitude_correct_checks _ i (correct finish)
  · exact arithmetic_checks_inactive _ i (Or.inl finish)

theorem finish_preserves_magnitudes (s : State) (i : Inputs) (finish : s.r0_nstate = 4) :
    (step s i).r1_ndivBy0Reg = s.r1_ndivBy0Reg ∧
    (step s i).r2_nshiftReg = s.r2_nshiftReg ∧
    (step s i).r5_nbReg = s.r5_nbReg ∧
    (step s i).r6_naValx2Reg = s.r6_naValx2Reg := by
  simp only [step, eval, finish]
  bv_decide

theorem finish_preserves_correct (s : State) (i : Inputs)
    (finish : s.r0_nstate = 4) (correct : MagnitudeCorrect s) : MagnitudeCorrect (step s i) := by
  have stable := finish_preserves_magnitudes s i finish
  unfold MagnitudeCorrect
  rw [stable.1, stable.2.1, stable.2.2.1, stable.2.2.2]
  exact correct

/-- A new finish state can only be entered on the final compute iteration. -/
theorem finish_predecessor (s : State) (i : Inputs) (finish : (step s i).r0_nstate = 4) :
    i.nreset = 0 ∧ (s.r0_nstate = 4 ∨ (s.r0_nstate = 3 ∧ s.r9_ncnt_5Fvalue = 63)) := by
  simp only [step, eval] at finish
  bv_decide

/-- All transitions other than the last compute edge preserve the invariant,
including arbitrary resets, stalls, acceptance, and setup transitions. -/
theorem finish_invariant_nonfinal (s : State) (i : Inputs) (correct : FinishInvariant s)
    (nonfinal : s.r0_nstate ≠ 3 ∨ s.r9_ncnt_5Fvalue ≠ 63) : FinishInvariant (step s i) := by
  intro finish
  have prior := finish_predecessor s i finish
  rcases prior.2 with prior | prior
  · exact finish_preserves_correct s i prior (correct prior)
  · rcases nonfinal with h | h
    · exact False.elim (h prior.1)
    · exact False.elim (h prior.2)

theorem compute_captured_run (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 3) (remaining : s.r9_ncnt_5Fvalue.toNat + n ≤ 64)
    (reset : ∀ t, t < n → (inputs t).nreset = 0) :
    (run s inputs n).r5_nbReg = s.r5_nbReg ∧
    (run s inputs n).r6_naValx2Reg = s.r6_naValx2Reg ∧
    (run s inputs n).r1_ndivBy0Reg = s.r1_ndivBy0Reg := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    have prior := ih (by omega) (fun t h => reset t (by omega))
    have control := compute_prefix n s inputs state (by omega) (fun t h => reset t (by omega))
    have edge := compute_preserves_captured (run s inputs n) (inputs n) control.1
    exact ⟨edge.1.trans prior.1, edge.2.1.trans prior.2.1,
      edge.2.2.2.2.2.2.trans prior.2.2⟩

/-- An aligned nonzero compute segment establishes the finish invariant on
its final edge. Captured operands and the zero flag are tied to the result. -/
theorem nonzero_segment_correct (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 3) (remaining : s.r9_ncnt_5Fvalue.toNat + n ≤ 64)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (flag : s.r1_ndivBy0Reg = 0)
    (bound : candidate s.r2_nshiftReg < 2 * s.r5_nbReg.toNat)
    (alignment : 2^n * s.r2_nshiftReg.toNat =
      36893488147419103232 * (s.r6_naValx2Reg.extractLsb' 1 64).toNat) :
    MagnitudeCorrect (run s inputs n) := by
  have result := compute_result n s inputs (s.r6_naValx2Reg.extractLsb' 1 64).toNat
    state remaining reset bound alignment
  have captured := compute_captured_run n s inputs state remaining reset
  unfold MagnitudeCorrect
  rw [captured.2.2, flag, if_neg (by decide), captured.1, captured.2.1]
  exact ⟨by omega, result.1, result.2⟩

end nRadix2Divider
