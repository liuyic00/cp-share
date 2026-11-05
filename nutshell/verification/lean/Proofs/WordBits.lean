import Proofs.ArithmeticBits
namespace NutShellProofs
open nNutCore

theorem word_sign_bit (x : BitVec 32) :
    BitVec.extractLsb' 31 1 x = BitVec.ofBool x.msb := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  by_cases h : k = 0
  · subst k
    simp [BitVec.getLsbD_extractLsb', BitVec.msb_eq_getLsbD_last]
  · have positive : 1 ≤ k := by omega
    simp [BitVec.getLsbD_of_ge _ _ positive]

theorem sign_extend_word (x : BitVec 32) :
    ((if BitVec.extractLsb' 31 1 x = 1 then BitVec.ofNat 32 4294967295 else 0) ++ x) =
      x.signExtend 64 := by
  rw [word_sign_bit]
  apply BitVec.eq_of_getLsbD_eq
  intro k
  rw [BitVec.getLsbD_append, BitVec.getLsbD_signExtend]
  by_cases low : k < 32
  · have bound : k < 64 := by omega
    simp [low, bound]
  · by_cases bound : k < 64
    · have upper : k - 32 < 32 := by omega
      cases msb : x.msb <;> simp [low, bound, msb, upper]
      change (BitVec.allOnes 32).getLsbD (k - 32) = true
      simp only [BitVec.getLsbD_allOnes, decide_eq_true upper]
    · have upper : 32 ≤ k - 32 := by omega
      cases msb : x.msb <;> simp [low, bound, msb, BitVec.getLsbD_of_ge _ _ upper]

theorem word_logical_shift (x : BitVec 32) (amount : Nat) :
    BitVec.extractLsb' 0 32 (((0 : BitVec 32) ++ x) >>> amount) = x >>> amount := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  by_cases low : k < 32
  · have bound : k < 64 := by omega
    have n32 : ¬32 ≤ k := by omega
    have n64 : ¬64 ≤ k := by omega
    by_cases shifted : amount + k < 32
    · simp [low, bound, shifted, Nat.add_comm]
    · have high : 32 ≤ k + amount := by omega
      simp [low, bound, shifted, Nat.add_comm, BitVec.getLsbD_of_ge x _ high]
      exact BitVec.getLsbD_of_ge x _ (by omega)
  · have high : 32 ≤ k := by omega
    simp [low, high]

theorem word_arithmetic_shift (x : BitVec 32) (amount : Nat) :
    BitVec.extractLsb' 0 32 ((x.signExtend 64).sshiftRight amount) = x.sshiftRight amount := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_sshiftRight,
    BitVec.getLsbD_signExtend, BitVec.msb_signExtend]
  by_cases low : k < 32
  · have bound : k < 64 := by omega
    have n32 : ¬32 ≤ k := by omega
    have n64 : ¬64 ≤ k := by omega
    by_cases shifted : amount + k < 32
    · have within : amount + k < 64 := by omega
      simp [low, bound, shifted, within, n32, n64]
    · by_cases within : amount + k < 64 <;> simp [low, bound, shifted, within, n32, n64]
  · have high : 32 ≤ k := by omega
    simp [low, high]

#print axioms word_logical_shift
#print axioms word_arithmetic_shift
#print axioms sign_extend_word
end NutShellProofs
