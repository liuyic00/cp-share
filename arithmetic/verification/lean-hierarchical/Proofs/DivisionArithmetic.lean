import Std

namespace HierarchicalDivision

/-- Most-significant-bit first restoring division of the low `width` bits. -/
def divideBits : Nat → Nat → Nat → Nat × Nat
  | 0, _, _ => (0, 0)
  | width + 1, dividend, divisor =>
    let previous := divideBits width (dividend / 2) divisor
    let candidate := 2 * previous.2 + dividend % 2
    if candidate < divisor then (2 * previous.1, candidate)
    else (2 * previous.1 + 1, candidate - divisor)

/-- The complete division identity and strict remainder bound are preserved
    while consuming the binary representation, without enumerating operands. -/
theorem invariant (width dividend divisor : Nat)
    (fits : dividend < 2 ^ width) (positive : 0 < divisor) :
    dividend = (divideBits width dividend divisor).1 * divisor +
      (divideBits width dividend divisor).2 ∧
    (divideBits width dividend divisor).2 < divisor := by
  induction width generalizing dividend with
  | zero =>
    have zero : dividend = 0 := by simpa using fits
    simp [divideBits, zero, positive]
  | succ width ih =>
    have smaller : dividend / 2 < 2 ^ width := by
      rw [Nat.pow_succ] at fits
      omega
    have previous := ih (dividend / 2) smaller
    have bit := Nat.mod_lt dividend (by decide : 0 < 2)
    have reconstruction := Nat.mod_add_div dividend 2
    simp only [divideBits]
    split
    · constructor
      · rw [Nat.mul_assoc]
        omega
      · assumption
    · constructor
      · rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
        omega
      · omega

theorem quotient_and_remainder (width dividend divisor : Nat)
    (fits : dividend < 2 ^ width) (positive : 0 < divisor) :
    (divideBits width dividend divisor).1 = dividend / divisor ∧
    (divideBits width dividend divisor).2 = dividend % divisor := by
  obtain ⟨identity, bound⟩ := invariant width dividend divisor fits positive
  constructor
  · have h := congrArg (fun value => value / divisor) identity
    simpa [Nat.mul_comm, Nat.mul_add_div positive, Nat.div_eq_of_lt bound] using h.symm
  · have h := congrArg (fun value => value % divisor) identity
    simpa [Nat.add_mod, Nat.mod_eq_of_lt bound] using h.symm

#print axioms quotient_and_remainder
end HierarchicalDivision
