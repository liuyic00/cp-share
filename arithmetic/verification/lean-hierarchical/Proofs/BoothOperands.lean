import Proofs.BoothArithmetic

namespace HierarchicalBooth

def quotient (a : Int) (k : Nat) : Int := a / (4 : Int) ^ k
def chunk (a : Int) (k : Nat) : Int := quotient a k % 4
def overlap (a : Int) : Nat → Int
  | 0 => 0
  | k + 1 => chunk a k / 2

def digit (a : Int) (k : Nat) : Int :=
  chunk a k % 2 - 2 * (chunk a k / 2) + overlap a k

theorem quotient_next (a : Int) (k : Nat) : quotient a (k + 1) = quotient a k / 4 := by
  simp only [quotient, Int.pow_succ, Int.ediv_ediv (Int.pow_nonneg (by decide : (0 : Int) ≤ 4))]

theorem operand_chunks (a : Int) (k : Nat) :
    chunk a k + 4 * quotient a (k + 1) = quotient a k := by
  rw [quotient_next]
  unfold chunk
  omega

/-- A 65-bit signed operand uses 33 radix-four groups, with sign extension
    in the final group. No assumption about its top two bits is needed. -/
theorem terminal_65 (a : BitVec 65) : quotient a.toInt 33 + overlap a.toInt 33 = 0 := by
  have lower := BitVec.le_toInt a
  have upper := BitVec.toInt_lt (x := a)
  change -18446744073709551616 ≤ a.toInt at lower
  change a.toInt < 18446744073709551616 at upper
  change a.toInt / 73786976294838206464 + (a.toInt / 18446744073709551616 % 4) / 2 = 0
  omega

theorem operand_value_65 (a : BitVec 65) : weighted 33 (digit a.toInt) = a.toInt := by
  have value := signed_recoding 33 (chunk a.toInt) (quotient a.toInt) (overlap a.toInt)
    (by intro k _; exact operand_chunks _ k) (by intro k _; rfl) rfl (terminal_65 a)
  simpa only [digit, quotient, Int.pow_zero, Int.ediv_one] using value

theorem operand_product_65 (a b : BitVec 65) :
    weighted 33 (fun k => digit a.toInt k * b.toInt) = a.toInt * b.toInt := by
  rw [weighted_product, operand_value_65]

end HierarchicalBooth
