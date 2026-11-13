import Proofs.BinaryPacking

namespace HierarchicalColumns

/-- Sum rows at each column before assigning binary place values. -/
def sumColumns : List (Nat → Nat) → Nat → Nat
  | [] => fun _ => 0
  | row :: rows => fun k => row k + sumColumns rows k

theorem weighted_zero (n : Nat) : weighted n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [weighted, ih]

/-- Reorganizing a bit matrix into columns preserves its weighted sum.
    This allows wiring proofs to be separated from each Booth row's arithmetic. -/
theorem weighted_sumColumns (n : Nat) (rows : List (Nat → Nat)) :
    weighted n (sumColumns rows) = (rows.map (weighted n)).sum := by
  induction rows with
  | nil => exact weighted_zero n
  | cons row rows ih =>
    change weighted n (fun k => row k + sumColumns rows k) =
      weighted n row + (rows.map (weighted n)).sum
    rw [weighted_add, ih]

/-- Row summation may also be performed directly at the output width. -/
theorem ofNat_sum (width : Nat) (values : List Nat) :
    BitVec.ofNat width values.sum = (values.map (BitVec.ofNat width)).sum := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.sum_cons, List.map_cons, BitVec.ofNat_add, ih]

theorem weighted_matrix_mod (width n : Nat) (rows : List (Nat → Nat)) :
    BitVec.ofNat width (weighted n (sumColumns rows)) =
      (rows.map (fun row => BitVec.ofNat width (weighted n row))).sum := by
  rw [weighted_sumColumns, ofNat_sum, List.map_map]
  rfl

end HierarchicalColumns
