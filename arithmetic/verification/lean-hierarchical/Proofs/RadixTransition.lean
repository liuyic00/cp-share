import Generated.Radix2Divider
import Proofs.DivisionArithmetic

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

attribute [local simp] v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61

/-- The bit-vector update performed during the compute state. -/
def advance (bits : BitVec 129) (divisor : BitVec 64) : BitVec 129 :=
  let candidate := BitVec.extractLsb' 64 65 bits
  let low := BitVec.extractLsb' 0 64 bits
  if divisor.toNat ≤ candidate.toNat then
    ((BitVec.extractLsb' 64 64 bits - divisor) ++ low) ++ 1#1
  else
    (BitVec.extractLsb' 64 64 bits ++ low) ++ 0#1

theorem compute_edge (s : State) (i : Inputs) (computing : s.r0_nstate = 3) :
    (step s i).r2_nshiftReg = advance s.r2_nshiftReg s.r5_nbReg := by
  have extend (d : BitVec 64) : (0#1 ++ d).toNat = d.toNat := by
    rw [BitVec.toNat_append]
    simp
  by_cases selected : s.r5_nbReg.toNat ≤ (BitVec.extractLsb' 64 65 s.r2_nshiftReg).toNat
  all_goals simp only [BitVec.extractLsb'_toNat, Nat.reducePow] at selected
  all_goals simp [step, eval_eq_spec, evalSpec, advance, computing, extend, selected]

theorem captured_divisor_stable (s : State) (i : Inputs) (computing : s.r0_nstate = 3) :
    (step s i).r5_nbReg = s.r5_nbReg := by
  simp [step, eval_eq_spec, evalSpec, computing]

def candidate (bits : BitVec 129) : Nat :=
  (BitVec.extractLsb' 64 65 bits).toNat

def remainderWord (bits : BitVec 129) (divisor : BitVec 64) : BitVec 64 :=
  if divisor.toNat ≤ candidate bits then BitVec.extractLsb' 64 64 bits - divisor
  else BitVec.extractLsb' 64 64 bits

def selectedBit (bits : BitVec 129) (divisor : BitVec 64) : Nat :=
  if divisor.toNat ≤ candidate bits then 1 else 0

/-- The truncated subtraction still computes the exact unbounded remainder
    when the restoring candidate bound holds, including its 65th bit. -/
theorem reduction (bits : BitVec 129) (divisor : BitVec 64)
    (bound : candidate bits < 2 * divisor.toNat) :
    candidate bits = selectedBit bits divisor * divisor.toNat +
      (remainderWord bits divisor).toNat ∧
    (remainderWord bits divisor).toNat < divisor.toNat := by
  have width := divisor.isLt
  have low : (BitVec.extractLsb' 64 64 bits).toNat = candidate bits % 18446744073709551616 := by
    simp only [candidate, BitVec.extractLsb'_toNat]
    omega
  unfold selectedBit remainderWord
  split
  · rw [BitVec.toNat_sub, low]
    simp only [Nat.one_mul]
    omega
  · rw [low]
    simp only [Nat.zero_mul, Nat.zero_add]
    omega

theorem append_value (a : BitVec m) (b : BitVec n) :
    (a ++ b).toNat = a.toNat * 2 ^ n + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt]
  simp only [Nat.shiftLeft_eq]

/-- This equation connects the actual hardware update to a base-two digit step. -/
theorem advance_value (bits : BitVec 129) (divisor : BitVec 64) :
    (advance bits divisor).toNat =
      2 * ((remainderWord bits divisor).toNat * 18446744073709551616 +
        (BitVec.extractLsb' 0 64 bits).toNat) + selectedBit bits divisor := by
  unfold advance remainderWord selectedBit candidate
  split <;> simp_all only [ite_true, ite_false, append_value, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod]
  all_goals omega

theorem candidate_value (bits : BitVec 129) :
    candidate bits = bits.toNat / 18446744073709551616 := by
  have width := bits.isLt
  simp only [candidate, BitVec.extractLsb'_toNat]
  omega

/-- A digit step preserves the unbounded division identity. The quotient digit
    is included on both sides because it occupies the newly vacated low bit. -/
theorem advance_balance (bits : BitVec 129) (divisor : BitVec 64)
    (bound : candidate bits < 2 * divisor.toNat) :
    (advance bits divisor).toNat +
        (selectedBit bits divisor * divisor.toNat) * 36893488147419103232 =
      2 * bits.toNat + selectedBit bits divisor := by
  have identity := (reduction bits divisor bound).1
  have low : (BitVec.extractLsb' 0 64 bits).toNat =
      bits.toNat % 18446744073709551616 := by
    simp [BitVec.extractLsb'_toNat]
  rw [candidate_value] at identity
  rw [advance_value, low]
  omega

/-- The restoring bound is inductive, so the digit lemma can be reused at every
    compute edge without assuming anything about later request inputs. -/
theorem advance_bound (bits : BitVec 129) (divisor : BitVec 64)
    (bound : candidate bits < 2 * divisor.toNat) :
    candidate (advance bits divisor) < 2 * divisor.toNat := by
  have remainder := (reduction bits divisor bound).2
  have low := (BitVec.extractLsb' 0 64 bits).isLt
  have digit : selectedBit bits divisor ≤ 1 := by
    unfold selectedBit
    split <;> omega
  rw [candidate_value, advance_value]
  omega

#print axioms advance_balance
#print axioms advance_bound
#print axioms reduction
#print axioms advance_value
end HierarchicalRadix
