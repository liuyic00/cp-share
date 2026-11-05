import Proofs.ArithmeticBits
namespace NutShellProofs
open nNutCore

theorem sign_bit_ofBool (x : BitVec w) :
    BitVec.extractLsb' (w - 1) 1 x = BitVec.ofBool x.msb := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  by_cases zero : k = 0
  · subst k
    simp [BitVec.getLsbD_extractLsb', BitVec.msb_eq_getLsbD_last]
  · have high : 1 ≤ k := by omega
    simp [BitVec.getLsbD_of_ge _ _ high]

theorem sign_extend_replication (x : BitVec w) (extra : Nat) :
    ((if BitVec.extractLsb' (w - 1) 1 x = 1 then BitVec.allOnes extra else 0) ++ x) =
      x.signExtend (extra + w) := by
  rw [sign_bit_ofBool]
  apply BitVec.eq_of_getLsbD_eq
  intro k
  rw [BitVec.getLsbD_append, BitVec.getLsbD_signExtend]
  by_cases low : k < w
  · have bound : k < extra + w := by omega
    simp [low, bound]
  · by_cases bound : k < extra + w
    · have upper : k - w < extra := by omega
      cases msb : x.msb <;>
        simp only [low, bound, msb, ↓reduceIte, BitVec.ofBool_false, BitVec.ofBool_true,
          BitVec.getLsbD_allOnes, BitVec.getLsbD_zero, decide_true, Bool.true_and,
          show ¬((0 : BitVec 1) = 1) by decide, upper]
      all_goals simp
    · have upper : ¬k - w < extra := by omega
      cases msb : x.msb <;>
        simp only [low, bound, msb, ↓reduceIte, BitVec.ofBool_false, BitVec.ofBool_true,
          BitVec.getLsbD_allOnes, BitVec.getLsbD_zero, decide_false, Bool.false_and,
          show ¬((0 : BitVec 1) = 1) by decide, upper]
      all_goals simp

#print axioms sign_extend_replication
end NutShellProofs
