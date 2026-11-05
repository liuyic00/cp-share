import Std
namespace RiscvMiniProofs

theorem ref_zero_append_nat {n w : Nat} (x : BitVec w) :
    ((0#n) ++ x).toNat = x.toNat := by
  simp only [BitVec.toNat_append]
  simp

theorem ref_zero_extend_shift_left (a : BitVec 32) (n : Nat) :
    BitVec.extractLsb' 0 32 (((0#31) ++ a).shiftLeft n) = a.shiftLeft n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [BitVec.getElem_append (n := 31) (m := 32), hj,
    show j < 63 by omega, show j-n < 32 by omega]

end RiscvMiniProofs
