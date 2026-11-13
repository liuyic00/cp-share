import Proofs.Radix2Divider
import Proofs.RestoringDivision

namespace nRadix2Divider
set_option maxRecDepth 4096

def candidate (sh : BitVec 129) : Nat := (BitVec.extractLsb' 64 65 sh).toNat

def lowCandidate (sh : BitVec 129) : BitVec 64 := BitVec.extractLsb' 64 64 sh

def reducedWord (sh : BitVec 129) (d : BitVec 64) : BitVec 64 :=
  if d.toNat ≤ candidate sh then lowCandidate sh - d else lowCandidate sh

def quotientBit (sh : BitVec 129) (d : BitVec 64) : BitVec 1 :=
  if d.toNat ≤ candidate sh then 1 else 0

def restoringStep (sh : BitVec 129) (d : BitVec 64) : BitVec 129 :=
  ((reducedWord sh d ++ BitVec.extractLsb' 0 64 sh) ++ quotientBit sh d)

theorem extend_toNat (d : BitVec 64) : (0#1 ++ d).toNat = d.toNat := by
  rw [BitVec.toNat_append]
  simp

/-- This is a refinement of the exported circuit, not a substitute model. -/
theorem compute_datapath (s : State) (i : Inputs) (state : s.r0_nstate = 3) :
    (step s i).r2_nshiftReg = restoringStep s.r2_nshiftReg s.r5_nbReg := by
  simp [step, eval, state, restoringStep, reducedWord, quotientBit,
    lowCandidate, candidate, extend_toNat]

/-- The compute phase uses the captured operands and controls, regardless of
    changes on the input interface. -/
theorem compute_preserves_captured (s : State) (i : Inputs) (state : s.r0_nstate = 3) :
    (step s i).r5_nbReg = s.r5_nbReg ∧
    (step s i).r6_naValx2Reg = s.r6_naValx2Reg ∧
    (step s i).r3_naSignReg = s.r3_naSignReg ∧
    (step s i).r4_nqSignReg = s.r4_nqSignReg ∧
    (step s i).r7_nctrlReg_5FisW = s.r7_nctrlReg_5FisW ∧
    (step s i).r8_nctrlReg_5FisHi = s.r8_nctrlReg_5FisHi ∧
    (step s i).r1_ndivBy0Reg = s.r1_ndivBy0Reg := by
  simp [step, eval, state]

theorem lowCandidate_toNat (sh : BitVec 129) :
    (lowCandidate sh).toNat = candidate sh % 18446744073709551616 := by
  simp only [lowCandidate, candidate, BitVec.extractLsb'_toNat]
  omega

/-- The hardware truncates the candidate before subtraction. Under the
    restoring invariant, its modular subtraction is the exact integer result,
    including candidates whose 65th bit is set. -/
theorem reducedWord_correct (sh : BitVec 129) (d : BitVec 64)
    (bound : candidate sh < 2 * d.toNat) :
    (reducedWord sh d).toNat = RestoringDivision.restore (candidate sh) d.toNat := by
  have hd := d.isLt
  unfold reducedWord RestoringDivision.restore
  split
  · rw [BitVec.toNat_sub, lowCandidate_toNat]
    omega
  · rw [lowCandidate_toNat]
    omega

theorem quotientBit_correct (sh : BitVec 129) (d : BitVec 64) :
    (quotientBit sh d).toNat = RestoringDivision.digit (candidate sh) d.toNat := by
  unfold quotientBit RestoringDivision.digit
  split <;> rfl

/-- The quotient bit and restored remainder selected by the physical circuit
    satisfy the unbounded-natural restoring-division invariant. -/
theorem selected_digit_correct (sh : BitVec 129) (d : BitVec 64)
    (positive : 0 < d.toNat) (bound : candidate sh < 2 * d.toNat) :
    candidate sh = (quotientBit sh d).toNat * d.toNat + (reducedWord sh d).toNat ∧
      (reducedWord sh d).toNat < d.toNat := by
  rw [quotientBit_correct, reducedWord_correct sh d bound]
  have h := RestoringDivision.restore_correct (candidate sh) d.toNat positive bound
  exact ⟨h.1, h.2.1⟩
theorem concatenate_step_toNat (r low : BitVec 64) (q : BitVec 1) :
    (((r ++ low) ++ q) : BitVec 129).toNat =
      2 * (r.toNat * 18446744073709551616 + low.toNat) + q.toNat := by
  rw [BitVec.toNat_append, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt q.isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt low.isLt]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

/-- Moving the concatenation by one bit feeds the old low word's MSB into
    the restored remainder. No high bits of this 65-bit candidate are lost. -/
theorem concatenate_candidate (r low : BitVec 64) (q : BitVec 1) :
    candidate ((r ++ low) ++ q) =
      2 * r.toNat + low.toNat / 9223372036854775808 := by
  unfold candidate
  rw [BitVec.extractLsb'_toNat, concatenate_step_toNat]
  simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have hr := r.isLt
  have hl := low.isLt
  have hq := q.isLt
  omega

theorem concatenate_low (r low : BitVec 64) (q : BitVec 1) :
    (BitVec.extractLsb' 0 64 ((r ++ low) ++ q)).toNat =
      (2 * low.toNat + q.toNat) % 18446744073709551616 := by
  rw [BitVec.extractLsb'_toNat, concatenate_step_toNat]
  simp only [Nat.shiftRight_zero, Nat.reducePow]
  omega

/-- The radix-2 candidate bound is an invariant of the actual generated
    datapath throughout its compute phase. -/
theorem compute_preserves_candidate_bound (s : State) (i : Inputs)
    (state : s.r0_nstate = 3)
    (bound : candidate s.r2_nshiftReg < 2 * s.r5_nbReg.toNat) :
    candidate (step s i).r2_nshiftReg < 2 * s.r5_nbReg.toNat := by
  rw [compute_datapath s i state]
  unfold restoringStep
  rw [concatenate_candidate, reducedWord_correct _ _ bound]
  have positive : 0 < s.r5_nbReg.toNat := by omega
  have h := RestoringDivision.restore_correct (candidate s.r2_nshiftReg)
    s.r5_nbReg.toNat positive bound
  have hl := (BitVec.extractLsb' 0 64 s.r2_nshiftReg).isLt
  omega
theorem split_shift_toNat (sh : BitVec 129) :
    sh.toNat = candidate sh * 18446744073709551616 +
      (BitVec.extractLsb' 0 64 sh).toNat := by
  simp only [candidate, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    Nat.reducePow]
  have hs := sh.isLt
  omega

private theorem packed_balance (z high low r d bit : Nat)
    (split : z = 18446744073709551616 * high + low)
    (selected : high = bit * d + r) (binary : bit ≤ 1) :
    2 * (18446744073709551616 * r + low) + bit +
      36893488147419103232 * d * bit = 2 * z + bit := by
  have cases : bit = 0 ∨ bit = 1 := by omega
  rcases cases with zero | one
  · subst bit
    simp only [Nat.zero_mul, Nat.zero_add] at selected
    simp only [Nat.mul_zero, Nat.add_zero]
    omega
  · subst bit
    simp only [Nat.one_mul] at selected
    simp only [Nat.mul_one]
    omega

/-- A complete compute edge preserves the integer balance of dividend,
    quotient bits, and the packed remainder/dividend register. -/
theorem restoringStep_balance (sh : BitVec 129) (d : BitVec 64)
    (bound : candidate sh < 2 * d.toNat) :
    (restoringStep sh d).toNat +
      36893488147419103232 * d.toNat * (quotientBit sh d).toNat =
      2 * sh.toNat + (quotientBit sh d).toNat := by
  have positive : 0 < d.toNat := by omega
  have selected := selected_digit_correct sh d positive bound
  have binary : (quotientBit sh d).toNat ≤ 1 := by
    rw [quotientBit_correct]
    exact (RestoringDivision.restore_correct (candidate sh) d.toNat positive bound).2.2
  unfold restoringStep
  rw [concatenate_step_toNat]
  rw [Nat.mul_comm (reducedWord sh d).toNat 18446744073709551616]
  apply packed_balance _ _ _ _ _ _ ?_ selected.1 binary
  simpa only [Nat.mul_comm (candidate sh) 18446744073709551616] using split_shift_toNat sh

/-- `q` is a proof-level accumulator of quotient bits; `scaled` is the
    correspondingly shifted captured dividend. Neither is an assumption about
    the result. The circuit's compute edge preserves their arithmetic relation. -/
theorem compute_preserves_balance (s : State) (i : Inputs) (q scaled : Nat)
    (state : s.r0_nstate = 3)
    (bound : candidate s.r2_nshiftReg < 2 * s.r5_nbReg.toNat)
    (balance : s.r2_nshiftReg.toNat + 36893488147419103232 * s.r5_nbReg.toNat * q =
      scaled + q) :
    let nextQ := 2 * q + (quotientBit s.r2_nshiftReg s.r5_nbReg).toNat
    (step s i).r2_nshiftReg.toNat + 36893488147419103232 * s.r5_nbReg.toNat * nextQ =
      2 * scaled + nextQ := by
  have h := restoringStep_balance s.r2_nshiftReg s.r5_nbReg bound
  rw [compute_datapath s i state]
  dsimp
  rw [Nat.mul_add, Nat.mul_left_comm _ 2 q]
  omega
end nRadix2Divider
