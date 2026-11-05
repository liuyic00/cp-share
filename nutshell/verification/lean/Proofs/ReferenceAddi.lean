import Proofs.AddiDecode
import Proofs.ReferenceSourceAddresses
namespace NutShellProofs
open nNutCore

/-- The reference sees the low 32 bits of the same committed EXU instruction. -/
theorem committed_reference_instruction (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    v14575 (step s i) next = BitVec.extractLsb' 0 32
      s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr := by
  simp only [v14575, v14560, v14559, v14558, commit, ↓reduceIte,
    v14573, v14572, v14571, v14570, v14569]
  rw [capture_decode_cf_instr s i next commit]
  rfl

theorem addi_match_low32 (instr : BitVec 64) (addi : IsADDI instr) :
    BitVec.extractLsb' 0 32 instr &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 19 := by
  have low := congrArg (BitVec.extractLsb' 0 32) addi
  simpa only [BitVec.extractLsb'_and] using low

theorem committed_reference_addi_match (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (addi : IsADDI s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v15071 (step s i) next = 1 := by
  have low := addi_match_low32 _ addi
  simp only [v15071, v15068, v15070, v15069,
    committed_reference_instruction s i next commit, low, ↓reduceIte]

theorem committed_reference_addi_uses_rs1 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (addi : IsADDI s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    referenceUsesRs1 (step s i) next = true :=
  reference_uses_rs1_of_addi_match _ _ commit (committed_reference_addi_match s i next commit addi)

#print axioms committed_reference_addi_uses_rs1
end NutShellProofs
