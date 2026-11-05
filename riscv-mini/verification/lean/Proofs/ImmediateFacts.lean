import Std
namespace RiscvMiniProofs

def immediateI (instruction : BitVec 32) : BitVec 32 :=
  (BitVec.extractLsb' 20 12 instruction).signExtend 32

def immediateU (instruction : BitVec 32) : BitVec 32 :=
  (BitVec.extractLsb' 12 20 instruction) ++ (0#12)

theorem redundant_sign_extension (x : BitVec 12) :
    (BitVec.replicate 19 (BitVec.extractLsb' 12 1 ((BitVec.extractLsb' 11 1 x) ++ x))) ++
      ((BitVec.extractLsb' 11 1 x) ++ x) = x.signExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_replicate,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_signExtend]
  by_cases lo : j < 12
  · simp [lo, show j < 13 by omega, hj]
  · by_cases edge : j < 13
    · have eq : j = 12 := by omega
      simp [eq, BitVec.msb_eq_getLsbD_last]
    · simp [Nat.mod_one, lo, edge, hj, show j-13 < 19 by omega, BitVec.msb_eq_getLsbD_last]

theorem dut_immediate_form (instruction : BitVec 32) :
    (BitVec.replicate 19 (BitVec.extractLsb' 12 1
      ((BitVec.extractLsb' 11 1 (BitVec.extractLsb' 20 12 instruction)) ++
        (BitVec.extractLsb' 20 12 instruction)))) ++
      ((BitVec.extractLsb' 11 1 (BitVec.extractLsb' 20 12 instruction)) ++
        (BitVec.extractLsb' 20 12 instruction)) = immediateI instruction :=
  redundant_sign_extension _

theorem immediateI_low5 (instruction : BitVec 32) :
    BitVec.extractLsb' 0 5 (immediateI instruction) = BitVec.extractLsb' 20 5 instruction := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [immediateI, BitVec.getLsbD_extractLsb', BitVec.getLsbD_signExtend]
  simp [hj, show j < 12 by omega, show j < 32 by omega]

#print axioms redundant_sign_extension

theorem reference_sign_extension (x : BitVec 12) :
    ((if BitVec.extractLsb' 11 1 x = 1 then (1048575#20) else (0#20)) ++ x) =
      x.signExtend 32 := by
  have bit : BitVec.extractLsb' 11 1 x = BitVec.ofBool x.msb := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have eq : j = 0 := by omega
    subst j
    simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool, BitVec.msb_eq_getLsbD_last]
  rw [bit, BitVec.signExtend_eq_append_of_le (by decide)]
  cases h : x.msb <;> simp [h] <;> rfl

#print axioms reference_sign_extension
end RiscvMiniProofs
