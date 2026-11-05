import Std
namespace RiscvMiniProofs

theorem one_and_bit (x : BitVec 1) : (1 : BitVec 1) &&& x = x := by
  change BitVec.allOnes 1 &&& x = x
  exact BitVec.allOnes_and

theorem zero_extend_shift_extract (a : BitVec 32) (n : Nat) :
    BitVec.extractLsb' 0 32 (((0#1) ++ a).sshiftRight n) = a.ushiftRight n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj33 : ¬33 ≤ j := by omega
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_sshiftRight,
    BitVec.getLsbD_append, BitVec.msb_append]
  simp only [Nat.zero_add, hj, hj33, decide_true, decide_false, Bool.true_and,
    Bool.not_false, BitVec.msb_zero, BitVec.getLsbD_zero]
  by_cases h : n+j < 32
  · simp [h, show n+j < 33 by omega]
  · simp [h, BitVec.getLsbD_of_ge a (n+j) (by omega)]

theorem sign_extend_shift_extract (a : BitVec 32) (n : Nat) :
    BitVec.extractLsb' 0 32 (((BitVec.extractLsb' 31 1 a) ++ a).sshiftRight n) =
      a.sshiftRight n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj32 : ¬32 ≤ j := by omega
  have hj33 : ¬33 ≤ j := by omega
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_sshiftRight,
    BitVec.getLsbD_append, BitVec.msb_eq_getLsbD_last]
  simp only [Nat.zero_add, hj, hj32, hj33, decide_true, decide_false, Bool.true_and,
    Bool.not_false]
  by_cases h : n+j < 32
  · simp [h, show n+j < 33 by omega]
  · by_cases h33 : n+j < 33
    · have he : n+j = 32 := by omega
      simp [he]
    · simp [h, h33]

theorem reverse_right_reverse (a : BitVec 32) (n : Nat) :
    (a.reverse.ushiftRight n).reverse = a.shiftLeft n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
  simp only [hj, decide_true, Bool.true_and]
  by_cases h : n ≤ j
  · have small : n + (32 - 1 - j) < 32 := by omega
    have same : 32 - 1 - (n + (32 - 1 - j)) = j - n := by omega
    simp [hj, show ¬j < n by omega, small, same, BitVec.getElem_reverse (w := 32), BitVec.getMsbD_eq_getLsbD]
    rfl
  · simp [show j < n by omega, BitVec.getLsbD_of_ge a.reverse (n + (31-j)) (by omega)]

#print axioms sign_extend_shift_extract
end RiscvMiniProofs
