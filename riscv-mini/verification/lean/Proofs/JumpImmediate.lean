import Std
namespace RiscvMiniProofs

def jumpBits (instruction : BitVec 32) : BitVec 21 :=
  (((BitVec.extractLsb' 31 1 instruction) ++ (BitVec.extractLsb' 12 8 instruction)) ++
    (BitVec.extractLsb' 20 1 instruction)) ++ ((BitVec.extractLsb' 21 10 instruction) ++ (0#1))

def immediateJ (instruction : BitVec 32) : BitVec 32 := (jumpBits instruction).signExtend 32

theorem jump_sign_replicate (x : BitVec 21) :
    (BitVec.replicate 11 (BitVec.extractLsb' 20 1 x)) ++ x = x.signExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_replicate,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_signExtend]
  by_cases lo : j < 21
  · simp [lo, hj]
  · simp [lo, hj, Nat.mod_one, show j-21 < 11 by omega, BitVec.msb_eq_getLsbD_last]

theorem jump_sign_conditional (x : BitVec 21) :
    ((if BitVec.extractLsb' 20 1 x = 1 then (2047#11) else (0#11)) ++ x) =
      x.signExtend 32 := by
  have bit : BitVec.extractLsb' 20 1 x = BitVec.ofBool x.msb := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have eq : j = 0 := by omega
    subst j
    simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool, BitVec.msb_eq_getLsbD_last]
  rw [bit, BitVec.signExtend_eq_append_of_le (by decide)]
  cases h : x.msb <;> simp [h] <;> rfl

theorem jump_middle_bits (instruction : BitVec 32) :
    (BitVec.extractLsb' 25 6 instruction) ++ (BitVec.extractLsb' 21 4 instruction) =
      BitVec.extractLsb' 21 10 instruction := by
  exact BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)

theorem extract_prefix (x : BitVec w) (middle start len : Nat) (bound : start + len ≤ middle) :
    BitVec.extractLsb' start len (BitVec.extractLsb' 0 middle x) =
      BitVec.extractLsb' start len x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show start+j < middle by omega]

theorem immediateJ_even (instruction : BitVec 32) :
    BitVec.extractLsb' 0 1 (immediateJ instruction) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have eq : j = 0 := by omega
  subst j
  simp [immediateJ, jumpBits, BitVec.getElem_signExtend,
    BitVec.getElem_append (n := 10) (m := 11),
    BitVec.getElem_append (n := 10) (m := 1)]

#print axioms immediateJ_even
#print axioms jump_sign_replicate
#print axioms jump_sign_conditional
#print axioms jump_middle_bits
end RiscvMiniProofs
