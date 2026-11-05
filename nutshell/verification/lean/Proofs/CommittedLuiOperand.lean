import Proofs.LuiSourceDecode
import Proofs.ReferenceLui
namespace NutShellProofs
open nNutCore

private theorem opcode_low32 (x : BitVec 64) :
    BitVec.extractLsb' 0 7 (BitVec.extractLsb' 0 32 x) = BitVec.extractLsb' 0 7 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [BitVec.getLsbD_extractLsb']
  by_cases small : k < 7
  · have bound : k < 32 := by omega
    simp [small, bound]
  · simp [small]

theorem committed_lui_reference_opcode (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (lui : BitVec.extractLsb' 0 7 s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr = 55) :
    BitVec.extractLsb' 0 7 (v14575 (step s i) next) = 55 := by
  simp only [v14575, v14560, v14559, v14558, commit, ↓reduceIte,
    v14573, v14572, v14571, v14570, v14569]
  rw [capture_decode_cf_instr s i next commit]
  simpa only [v25333, v11547, opcode_low32] using lui

theorem committed_lui_operand_zero (s : State) (i next : Inputs)
    (decode : ExecuteLuiSource1Decoded s) (commit : v9 (step s i) next = 1)
    (lui : BitVec.extractLsb' 0 7 s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr = 55) :
    (step s i).g50.r1620_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc1 = 0 := by
  have valid := commit_requires_execute_valid s i next commit
  have address := decode valid lui
  have capture := capture_decode_data_src1 s i next commit
  apply capture.trans
  simp [v25503, v25502, v25500, v25465, v25499, v25501, address]

theorem committed_lui_operand_reference (s : State) (i next : Inputs)
    (decode : ExecuteLuiSource1Decoded s) (commit : v9 (step s i) next = 1)
    (zero : ReferenceZero (step s i))
    (lui : BitVec.extractLsb' 0 7 s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr = 55) :
    (step s i).g50.r1620_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc1 =
      v15632 (step s i) next := by
  rw [committed_lui_operand_zero s i next decode commit lui]
  exact (reference_lui_rs1_zero _ _ zero (committed_lui_reference_opcode s i next commit lui)).symm

theorem committed_lui_operand_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (lui : BitVec.extractLsb' 0 7 (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr = 55) :
    (run initial inputs (t + 2)).g50.r1620_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc1 =
      v15632 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  exact committed_lui_operand_reference _ _ _ (lui_source1_decode_run initial inputs reset t).2
    commit (reference_zero_run initial inputs reset (t + 1)) lui

#print axioms committed_lui_operand_run
end NutShellProofs
