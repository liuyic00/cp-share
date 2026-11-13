import Proofs.BoothRecoding

namespace BoothRecoding

def operandPairs : Nat → BitVec 66 → List Pair
  | 0, _ => []
  | n + 1, x => (x.getLsbD 0, x.getLsbD 1) :: operandPairs n (x.sshiftRight 2)

def remainingBits : Nat → BitVec 66 → BitVec 66
  | 0, x => x
  | n + 1, x => remainingBits n (x.sshiftRight 2)

theorem split_pair (x : BitVec 66) :
    x.toInt = bit (x.getLsbD 0) + 2 * bit (x.getLsbD 1) + 4 * (x.sshiftRight 2).toInt := by
  have splitBits : x = (x.extractLsb' 2 64 ++ BitVec.ofBool (x.getLsbD 1)) ++
      BitVec.ofBool (x.getLsbD 0) := by bv_decide
  have shifted : x.sshiftRight 2 = (x.extractLsb' 2 64).signExtend 66 := by bv_decide
  have value := congrArg BitVec.toInt splitBits
  rw [BitVec.toInt_append, BitVec.toInt_append] at value
  rw [shifted, BitVec.toInt_signExtend_of_le (by decide)]
  cases h0 : x.getLsbD 0 <;> cases h1 : x.getLsbD 1 <;>
    simp only [h0, h1] at value ⊢ <;> simp [bit] at value ⊢ <;> omega

theorem remaining_shift (n : Nat) (x : BitVec 66) :
    remainingBits n x = x.sshiftRight (2*n) := by
  induction n generalizing x with
  | zero => simp [remainingBits]
  | succ n ih =>
    rw [remainingBits, ih, ← BitVec.sshiftRight_add]
    congr 1
    omega

theorem operand_top (n : Nat) (x : BitVec 66) (previous : Bool) :
    top previous (operandPairs (n+1) x) = (remainingBits n x).getLsbD 1 := by
  induction n generalizing x previous with
  | zero => rfl
  | succ n ih => exact ih (x.sshiftRight 2) (x.getLsbD 1)

theorem operand_recoded (n : Nat) (x : BitVec 66) (previous : Bool) :
    recoded previous (operandPairs n x) = x.toInt + bit previous -
      4^n * ((remainingBits n x).toInt + bit (top previous (operandPairs n x))) := by
  induction n generalizing x previous with
  | zero => simp [operandPairs, recoded, remainingBits, top]
  | succ n ih =>
    rw [operandPairs, recoded, ih]
    have splitBits := split_pair x
    simp only [remainingBits, top, digit, Int.pow_succ, Int.mul_add,
      Int.mul_sub, Int.mul_assoc, Int.mul_left_comm (4^n) 4]
    omega

/-- The 33 overlapping windows of the sign-extended 65-bit multiplier
recode exactly its signed integer value. -/
theorem operand_recoded_65 (a : BitVec 65) :
    recoded false (operandPairs 33 (a.signExtend 66)) = a.toInt := by
  rw [operand_recoded, operand_top 32, remaining_shift, remaining_shift]
  have final : ((a.signExtend 66).sshiftRight 66).toInt +
      bit (((a.signExtend 66).sshiftRight 64).getLsbD 1) = 0 := by
    have shift : (a.signExtend 66).sshiftRight 66 = if a.msb then -1 else 0 := by bv_decide
    have signBit : ((a.signExtend 66).sshiftRight 64).getLsbD 1 = a.msb := by bv_decide
    rw [shift, signBit]
    cases a.msb <;> decide
  change (a.signExtend 66).toInt + bit false - 4^33 *
    (((a.signExtend 66).sshiftRight 66).toInt + bit (((a.signExtend 66).sshiftRight 64).getLsbD 1)) = _
  rw [final, BitVec.toInt_signExtend_of_le (by decide)]
  simp [bit]

def wideProducts (b : BitVec 65) (previous : Bool) : List Pair → BitVec 130
  | [] => 0
  | p :: ps => b.signExtend 130 * BitVec.ofInt 130 (digit previous p) +
      4 * wideProducts b p.2 ps

theorem wideProducts_eq (b : BitVec 65) (previous : Bool) (ps : List Pair) :
    wideProducts b previous ps = BitVec.ofInt 130 (partialProducts b.toInt previous ps) := by
  induction ps generalizing previous with
  | nil => rfl
  | cons p ps ih =>
    simp only [wideProducts, partialProducts, ih, BitVec.ofInt_add, BitVec.ofInt_mul]
    change BitVec.ofInt 130 b.toInt * BitVec.ofInt 130 (digit previous p) + _ = _
    rw [BitVec.mul_comm (BitVec.ofInt 130 b.toInt)]
    rfl

/-- The complete 33-row weighted sum is the signed 130-bit product. -/
theorem wide_operand_product (a b : BitVec 65) :
    wideProducts b false (operandPairs 33 (a.signExtend 66)) =
      BitVec.ofInt 130 (a.toInt * b.toInt) := by
  rw [wideProducts_eq, partialProducts_eq, operand_recoded_65]

end BoothRecoding
