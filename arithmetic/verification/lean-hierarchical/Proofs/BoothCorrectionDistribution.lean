import Proofs.BoothBitVecSum

namespace HierarchicalBooth

theorem weightedBits_add (n : Nat) (a b : Nat → BitVec 130) :
    weightedBits n (fun k => a k + b k) = weightedBits n a + weightedBits n b := by
  induction n generalizing a b with
  | zero => simp [weightedBits]
  | succ n ih =>
    simp only [weightedBits, ih, BitVec.mul_add]
    ac_rfl

theorem weightedBits_scale (n : Nat) (a : Nat → BitVec 130) (factor : BitVec 130) :
    weightedBits n (fun k => factor * a k) = factor * weightedBits n a := by
  induction n generalizing a with
  | zero => simp [weightedBits]
  | succ n ih =>
    simp only [weightedBits, ih, BitVec.mul_add]
    ac_rfl

theorem weightedBits_snoc (n : Nat) (a : Nat → BitVec 130) :
    weightedBits (n + 1) a = weightedBits n a + BitVec.ofNat 130 (4^n) * a n := by
  induction n generalizing a with
  | zero => simp [weightedBits]
  | succ n ih =>
    change a 0 + 4 * weightedBits (n + 1) (fun k => a (k + 1)) =
      (a 0 + 4 * weightedBits n (fun k => a (k + 1))) +
        BitVec.ofNat 130 (4^(n + 1)) * a (n + 1)
    rw [ih]
    simp only [Nat.pow_succ, BitVec.ofNat_mul, BitVec.mul_add,
      show BitVec.ofNat 130 4 = (4 : BitVec 130) from rfl]
    ac_rfl

/-- Each correction can be placed in the low two bits of the following row.
    The final row's correction is retained separately at the same weight. -/
theorem distribute_corrections (n : Nat) (raw correction : Nat → BitVec 130) :
    raw 0 + weightedBits n (fun k => 4 * raw (k + 1) + correction k) +
      BitVec.ofNat 130 (4^n) * correction n =
    weightedBits (n + 1) (fun k => raw k + correction k) := by
  rw [weightedBits_add, weightedBits_scale, weightedBits_add,
    weightedBits_snoc n correction]
  rw [show weightedBits (n + 1) raw = raw 0 + 4 * weightedBits n (fun k => raw (k + 1)) from rfl]
  ac_rfl

end HierarchicalBooth
