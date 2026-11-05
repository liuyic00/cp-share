import Proofs.FetchTransfer
namespace RiscvMiniProofs
open nCoreSoc

theorem fetch_target_bits (target : BitVec 32) :
    BitVec.extractLsb' 0 32 (((0#1) ++ (target.ushiftRight 1)).shiftLeft 1) =
      (BitVec.extractLsb' 1 31 target) ++ (0#1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight]
  by_cases lo : j = 0
  · subst j
    simp
  · simp [BitVec.getElem_append (n := 1) (m := 32), BitVec.getElem_ushiftRight,
      show j < 33 by omega, show ¬j < 1 by omega, show 1 ≤ j by omega,
      show j-1 < 32 by omega, show j-1 < 31 by omega, hj,
      show j-1+1=j by omega, show 1+(j-1)=j by omega]

theorem fetch_increment_bits (pc : BitVec 33) :
    BitVec.extractLsb' 0 32 (BitVec.extractLsb' 0 33 (((0#1) ++ pc) + (4#34))) =
      BitVec.extractLsb' 0 32 pc + 4 := by
  apply BitVec.eq_of_toNat_eq
  have bound := pc.isLt
  have z : ((0#1) ++ pc).toNat = pc.toNat := by
    simp only [BitVec.toNat_append]
    simp
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_add, z,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.div_one,
    Nat.reduceMod]
  dsimp at *
  omega

theorem fetch_target_low32 (s : State) (i : Inputs) :
    BitVec.extractLsb' 0 32 (v8497 s i) =
      (BitVec.extractLsb' 1 31 (v8041 s i)) ++ (0#1) :=
  fetch_target_bits (v8041 s i)

theorem fetch_increment_low32 (s : State) (i : Inputs) :
    BitVec.extractLsb' 0 32 (v8502 s i) =
      BitVec.extractLsb' 0 32 s.g4.r137_ndut_5Fdpath_5Fpc + 4 :=
  fetch_increment_bits s.g4.r137_ndut_5Fdpath_5Fpc

theorem fetch_pc_low32_step (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i)
    (noReturn : s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst ≠ 268435571) :
    BitVec.extractLsb' 0 32 (step s i).g4.r137_ndut_5Fdpath_5Fpc =
      if v8475 s i = 1 then (BitVec.extractLsb' 1 31 (v8041 s i)) ++ (0#1)
      else if v8473 s i = 2 then BitVec.extractLsb' 0 32 s.g4.r137_ndut_5Fdpath_5Fpc
      else BitVec.extractLsb' 0 32 s.g4.r137_ndut_5Fdpath_5Fpc + 4 := by
  rw [(fetch_transfer_step s i reset env noReturn).fetch_pc]
  split
  · exact fetch_target_low32 s i
  · split
    · rfl
    · exact fetch_increment_low32 s i

#print axioms fetch_pc_low32_step
#print axioms fetch_target_bits
#print axioms fetch_increment_bits
end RiscvMiniProofs
