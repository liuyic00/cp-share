import Std

namespace HierarchicalMultiply

/-- Least-significant-digit expansion of multiplication. -/
def digitProduct (a b : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (a % 2) * b + 2 * digitProduct (a / 2) b n

/-- Consuming every binary digit produces the mathematical product, with no
    machine-width assumptions on the multiplicand. -/
theorem digitProduct_complete (n a b : Nat) (fits : a < 2 ^ n) :
    digitProduct a b n = a * b := by
  induction n generalizing a with
  | zero =>
    have zero : a = 0 := by simpa using fits
    simp [zero, digitProduct]
  | succ n ih =>
    have half : a / 2 < 2 ^ n := by
      rw [Nat.pow_succ] at fits
      omega
    rw [digitProduct, ih (a / 2) half, ← Nat.mul_assoc, ← Nat.add_mul, Nat.mod_add_div]

/-- A signed top digit changes its unsigned contribution from plus one to
    minus one, subtracting one full-width copy of the multiplicand. -/
theorem signed_top_digit (low b width : Nat) :
    (low : Int) * b - (2 ^ width : Nat) * (b : Int) =
      ((low : Int) - (2 ^ width : Nat)) * b := by
  rw [Int.sub_mul]

/-- The complete digit expansion yields both halves of the exact 128-bit
    unsigned product of two 64-bit operands. -/
theorem word_product (a b : BitVec 64) :
    BitVec.ofNat 128 (digitProduct a.toNat b.toNat 64) =
      a.setWidth 128 * b.setWidth 128 := by
  rw [digitProduct_complete 64 a.toNat b.toNat a.isLt]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_setWidth]

def shiftAdd (weight value : Nat) : Nat := value / 2 + (value % 2) * weight

def shiftAddMany (weight : Nat) : Nat → Nat → Nat
  | 0, value => value
  | n + 1, value => shiftAddMany weight n (shiftAdd weight value)

/-- Adding an even contribution does not change the multiplier digit being
    consumed, and halves that contribution on the next edge. -/
theorem shiftAdd_even (weight value carry : Nat) :
    shiftAdd weight (value + carry * 2) = shiftAdd weight value + carry := by
  unfold shiftAdd
  rw [Nat.add_mul_div_right _ _ (by decide : 0 < 2), Nat.add_mul_mod_self_right]
  omega

/-- A contribution aligned above all remaining digits moves down without
    affecting any of those digits. -/
theorem shiftAddMany_translation (weight n value carry : Nat) :
    shiftAddMany weight n (value + carry * 2 ^ n) =
      shiftAddMany weight n value + carry := by
  induction n generalizing value with
  | zero => simp [shiftAddMany]
  | succ n ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc, shiftAddMany, shiftAdd_even, ih]
    rfl

/-- Closed form of the add-and-shift multiplier after any prefix of digits. -/
theorem shiftAddMany_value (w n a b : Nat) (within : n ≤ w + 1) :
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
      conv => lhs; rw [splitPower, Nat.pow_add]
      simp [Nat.mul_assoc]
    rw [shiftAddMany, shiftAdd, contribution, shiftAddMany_translation,
      ih (a / 2) (by omega), digitProduct, exponent, nextExponent,
      Nat.pow_succ, Nat.div_div_eq_div_mul]
    simp [Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem shiftAddMany_succ_end (weight n value : Nat) :
    shiftAddMany weight (n + 1) value = shiftAdd weight (shiftAddMany weight n value) := by
  induction n generalizing value with
  | zero => rfl
  | succ n ih =>
    rw [shiftAddMany, ih]
    rfl

#print axioms shiftAddMany_value
#print axioms shiftAddMany_translation
#print axioms word_product
#print axioms digitProduct_complete
end HierarchicalMultiply
