import Proofs.BoothArithmetic

namespace HierarchicalBooth

def weightedBits : Nat → (Nat → BitVec 130) → BitVec 130
  | 0, _ => 0
  | n + 1, rows => rows 0 + 4 * weightedBits n (fun k => rows (k + 1))

theorem weightedBits_ofInt (n : Nat) (rows : Nat → Int) :
    weightedBits n (fun k => BitVec.ofInt 130 (rows k)) =
      BitVec.ofInt 130 (weighted n rows) := by
  induction n generalizing rows with
  | zero => rfl
  | succ n ih =>
    simp only [weightedBits, weighted, ih, BitVec.ofInt_add, BitVec.ofInt_mul]
    rfl

end HierarchicalBooth
