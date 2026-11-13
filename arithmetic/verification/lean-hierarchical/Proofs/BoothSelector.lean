import Proofs.BoothOperands

namespace HierarchicalBooth

def coefficient (code : BitVec 3) : Int :=
  if code = 1 ∨ code = 2 then 1
  else if code = 3 then 2
  else if code = 4 then -2
  else if code = 5 ∨ code = 6 then -1
  else 0

/-- The selector's negative rows are one's complements; correction bits are
    carried separately in the array implementation. -/
def rawPartial (code : BitVec 3) (b : BitVec 66) : BitVec 66 :=
  if code = 1 ∨ code = 2 then b
  else if code = 3 then b <<< 1
  else if code = 4 then (~~~b) <<< 1
  else if code = 5 ∨ code = 6 then ~~~b
  else 0

def correction (code : BitVec 3) : BitVec 66 :=
  if code = 4 then 2 else if code = 5 ∨ code = 6 then 1 else 0

theorem coefficient_bits (code : BitVec 3) :
    coefficient code = (code.toNat % 2 : Int) + (code.toNat / 2 % 2 : Int) -
      2 * (code.toNat / 4 : Int) := by
  have all : ∀ x : BitVec 3,
      coefficient x = (x.toNat % 2 : Int) + (x.toNat / 2 % 2 : Int) -
        2 * (x.toNat / 4 : Int) := by
    unfold coefficient
    decide
  exact all code

theorem corrected_partial (code : BitVec 3) (b : BitVec 66) :
    rawPartial code b + correction code = BitVec.ofInt 66 (coefficient code) * b := by
  have cases : code = 0 ∨ code = 1 ∨ code = 2 ∨ code = 3 ∨
      code = 4 ∨ code = 5 ∨ code = 6 ∨ code = 7 := by bv_decide
  rcases cases with h | h | h | h | h | h | h | h <;> subst code <;>
    simp [rawPartial, correction, coefficient]
  all_goals first
    | change ((~~~b) <<< 1) + 2#66 = -(2#66) * b
      rw [BitVec.neg_mul, BitVec.two_mul]
      bv_decide
    | bv_decide

theorem corrected_signed_partial (code : BitVec 3) (b : BitVec 65) :
    rawPartial code (b.signExtend 66) + correction code =
      BitVec.ofInt 66 (coefficient code * b.toInt) := by
  rw [corrected_partial, BitVec.ofInt_mul]
  rfl

theorem encoded_coefficient (c r : Int) (hc : 0 ≤ c ∧ c < 4) (hr : 0 ≤ r ∧ r < 2) :
    coefficient (BitVec.ofInt 3 (2 * c + r)) = c % 2 - 2 * (c / 2) + r := by
  rw [coefficient_bits]
  simp only [BitVec.toNat_ofInt]
  omega

def operandCode (a : Int) (k : Nat) : BitVec 3 :=
  BitVec.ofInt 3 (2 * chunk a k + overlap a k)

theorem operand_coefficient (a : Int) (k : Nat) :
    coefficient (operandCode a k) = digit a k := by
  apply encoded_coefficient
  · unfold chunk
    omega
  · cases k with
    | zero => simp [overlap]
    | succ k =>
      simp only [overlap, chunk]
      omega

theorem selected_product_65 (a b : BitVec 65) :
    weighted 33 (fun k => coefficient (operandCode a.toInt k) * b.toInt) =
      a.toInt * b.toInt := by
  simp only [operand_coefficient]
  exact operand_product_65 a b

end HierarchicalBooth
