import Std

namespace HierarchicalSignedMultiply

def shiftAdd (weight value : Int) : Int := value / 2 + (value % 2) * weight

def shiftAddMany (weight : Int) : Nat → Int → Int
  | 0, value => value
  | n + 1, value => shiftAddMany weight n (shiftAdd weight value)

theorem shiftAdd_even (weight value carry : Int) :
    shiftAdd weight (value + carry * 2) = shiftAdd weight value + carry := by
  unfold shiftAdd
  rw [Int.add_mul_ediv_right _ _ (by decide : (2 : Int) ≠ 0)]
  have parity : (value + carry * 2) % 2 = value % 2 := by omega
  rw [parity]
  omega

theorem shiftAddMany_translation (weight : Int) (n : Nat) (value carry : Int) :
    shiftAddMany weight n (value + carry * 2 ^ n) =
      shiftAddMany weight n value + carry := by
  induction n generalizing value with
  | zero => simp [shiftAddMany]
  | succ n ih =>
    rw [Int.pow_succ, ← Int.mul_assoc, shiftAddMany, shiftAdd_even, ih]
    rfl

theorem shiftAddMany_succ_end (weight : Int) (n : Nat) (value : Int) :
    shiftAddMany weight (n + 1) value = shiftAdd weight (shiftAddMany weight n value) := by
  induction n generalizing value with
  | zero => rfl
  | succ n ih =>
    rw [shiftAddMany, ih]
    rfl

def digitProduct (a b : Int) : Nat → Int
  | 0 => 0
  | n + 1 => (a % 2) * b + 2 * digitProduct (a / 2) b n

theorem shiftAddMany_value (w n : Nat) (a b : Int) (within : n ≤ w + 1) :
    shiftAddMany (b * 2 ^ w) n a =
      a / 2 ^ n + digitProduct a b n * 2 ^ (w + 1 - n) := by
  induction n generalizing a with
  | zero => simp [shiftAddMany, digitProduct]
  | succ n ih =>
    have splitPower : w = (w - n) + n := by omega
    have exponent : w + 1 - n = (w - n) + 1 := by omega
    have nextExponent : w + 1 - (n + 1) = w - n := by omega
    have contribution : (a % 2) * (b * 2 ^ w) =
        ((a % 2) * b * 2 ^ (w - n)) * 2 ^ n := by
      conv => lhs; rw [splitPower, Int.pow_add]
      simp [Int.mul_assoc]
    rw [shiftAddMany, shiftAdd, contribution, shiftAddMany_translation,
      ih (a / 2) (by omega), digitProduct, exponent, nextExponent,
      Int.pow_succ, Int.ediv_ediv (by decide : (0 : Int) ≤ 2)]
    simp [Int.pow_succ, Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
      Int.add_assoc, Int.add_comm, Int.add_left_comm]

/-- Digit expansion selects exactly the consumed low bits, also when the
    multiplicand is a negative integer. -/
theorem digitProduct_value (n : Nat) (a b : Int) :
    digitProduct a b n = (a - a / 2 ^ n * 2 ^ n) * b := by
  induction n generalizing a with
  | zero => simp [digitProduct]
  | succ n ih =>
    have remainder : a % 2 = a - a / 2 * 2 := by omega
    rw [digitProduct, ih, remainder, Int.ediv_ediv (by decide : (0 : Int) ≤ 2)]
    simp [Int.pow_succ, Int.sub_mul, Int.mul_sub, Int.mul_add, Int.add_mul,
      Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega

#print axioms digitProduct_value
#print axioms shiftAddMany_value
#print axioms shiftAddMany_translation
end HierarchicalSignedMultiply
