import Proofs.JumpImmediate
namespace RiscvMiniProofs
def branchBits (instruction : BitVec 32) : BitVec 13 :=
  (((BitVec.extractLsb' 31 1 instruction) ++ (BitVec.extractLsb' 7 1 instruction)) ++
    (BitVec.extractLsb' 25 6 instruction)) ++ ((BitVec.extractLsb' 8 4 instruction) ++ (0#1))
def immediateB (instruction : BitVec 32) : BitVec 32 := (branchBits instruction).signExtend 32
theorem branch_sign_replicate (x : BitVec 13) :
    (BitVec.replicate 19 (BitVec.extractLsb' 12 1 x)) ++ x = x.signExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_replicate,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_signExtend]
  by_cases lo : j < 13
  · simp [lo, hj]
  · simp [lo, hj, Nat.mod_one, show j-13 < 19 by omega, BitVec.msb_eq_getLsbD_last]

theorem branch_sign_conditional (x : BitVec 13) :
    ((if BitVec.extractLsb' 12 1 x = 1 then (524287#19) else (0#19)) ++ x) =
      x.signExtend 32 := by
  have bit : BitVec.extractLsb' 12 1 x = BitVec.ofBool x.msb := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have eq : j = 0 := by omega
    subst j
    simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool, BitVec.msb_eq_getLsbD_last]
  rw [bit, BitVec.signExtend_eq_append_of_le (by decide)]
  cases h : x.msb <;> simp [h] <;> rfl

theorem immediateB_even (instruction : BitVec 32) :
    BitVec.extractLsb' 0 1 (immediateB instruction) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have eq : j = 0 := by omega
  subst j
  simp [immediateB, branchBits, BitVec.getElem_signExtend,
    BitVec.getElem_append (n := 8) (m := 5),
    BitVec.getElem_append (n := 4) (m := 1)]
#print axioms immediateB_even
end RiscvMiniProofs
