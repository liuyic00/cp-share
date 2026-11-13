import Std.Tactic

namespace ColumnSum

theorem add_equalities {a b c d : Nat} (first : a = b) (second : c = d) :
    a + c = b + d := by rw [first, second]

/-- Extend a weighted prefix when one column preserves its input sum. -/
theorem extend (weight beforeIn beforeOut input output previous carry : Nat)
    (earlier : beforeIn = beforeOut + weight * previous)
    (column : input + previous = output + 2 * carry) :
    beforeIn + weight * input =
      beforeOut + weight * output + (2 * weight) * carry := by
  calc
    beforeIn + weight * input = beforeOut + weight * (input + previous) := by
      rw [earlier, Nat.mul_add]
      omega
    _ = beforeOut + weight * (output + 2 * carry) := by rw [column]
    _ = beforeOut + weight * output + (2 * weight) * carry := by
      rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm weight 2]
      omega

end ColumnSum
