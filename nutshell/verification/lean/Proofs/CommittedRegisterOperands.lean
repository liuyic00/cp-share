import Proofs.OperandInvariant
import Proofs.ReferenceSourceAddresses
import Proofs.SourceDecode
namespace NutShellProofs
open nNutCore

theorem committed_register_operand_1_dut (s : State) (i next : Inputs)
    (invariant : RegisterOperand1Aligned s) (commit : v9 (step s i) next = 1)
    (kind : s.g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = 0) :
    (step s i).g50.r1620_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc1 =
      dutRead.v25201 (step s i) next s.g48.r1555_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc1 := by
  have valid := commit_requires_execute_valid s i next commit
  obtain ⟨reset, flush⟩ := next_commit_controls s i next commit
  have operand := invariant i next valid kind reset flush
  have capture := capture_decode_data_src1 s i next commit
  apply capture.trans
  by_cases zero : s.g48.r1555_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc1 = 0
  · rw [zero, dutRead.read_0]
    simp [v25503, v25502, v25500, v25499, v25501, v25465, zero]
  · have nz : v25465 s i ≠ v25499 s i := zero
    have compare : v25500 s i = 0 := by rw [v25500, if_neg nz]
    simpa only [v25503, v25502, compare, ↓reduceIte] using operand

theorem committed_register_operand_1_reference (s : State) (i next : Inputs)
    (invariant : RegisterOperand1Aligned s) (commit : v9 (step s i) next = 1)
    (kind : s.g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = 0)
    (aligned : ArchitecturalRegistersAligned (step s i)) (zero : ReferenceZero (step s i))
    (address : s.g48.r1555_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc1 = v15551 (step s i) next) :
    (step s i).g50.r1620_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc1 = v15632 (step s i) next := by
  rw [committed_register_operand_1_dut s i next invariant commit kind, address, specRead2.actual]
  rw [← dut_read_ports_same]
  exact register_read_muxes_agree2 _ _ _ aligned zero

#print axioms committed_register_operand_1_reference

theorem committed_register_operand_2_dut (s : State) (i next : Inputs)
    (invariant : RegisterOperand2Aligned s) (commit : v9 (step s i) next = 1)
    (kind : s.g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = 0) :
    (step s i).g50.r1621_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc2 =
      dutRead.v25201 (step s i) next s.g48.r1556_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc2 := by
  have valid := commit_requires_execute_valid s i next commit
  obtain ⟨reset, flush⟩ := next_commit_controls s i next commit
  have operand := invariant i next valid kind reset flush
  have capture := capture_decode_data_src2 s i next commit
  apply capture.trans
  by_cases zero : s.g48.r1556_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc2 = 0
  · rw [zero, dutRead.read_0]
    simp [v25509, v25508, v25506, v25505, v25507, v25468, zero]
  · have nz : v25468 s i ≠ v25505 s i := zero
    have compare : v25506 s i = 0 := by rw [v25506, if_neg nz]
    simpa only [v25509, v25508, compare, ↓reduceIte] using operand

theorem committed_register_operand_2_reference (s : State) (i next : Inputs)
    (invariant : RegisterOperand2Aligned s) (commit : v9 (step s i) next = 1)
    (kind : s.g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = 0)
    (aligned : ArchitecturalRegistersAligned (step s i)) (zero : ReferenceZero (step s i))
    (address : s.g48.r1556_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc2 = v15282 (step s i) next) :
    (step s i).g50.r1621_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc2 = v15394 (step s i) next := by
  rw [committed_register_operand_2_dut s i next invariant commit kind, address, specRead.actual]
  exact register_read_muxes_agree _ _ _ aligned zero

#print axioms committed_register_operand_2_reference


/-- Connect an instruction-field decoder invariant to the actual reference read port. -/
theorem committed_register_operand_1_decoded (s : State) (i next : Inputs)
    (invariant : RegisterOperand1Aligned s) (commit : v9 (step s i) next = 1)
    (kind : s.g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = 0)
    (aligned : ArchitecturalRegistersAligned (step s i)) (zero : ReferenceZero (step s i))
    (used : referenceUsesRs1 (step s i) next = true)
    (decoded : s.g48.r1555_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc1 =
      BitVec.extractLsb' 15 5 s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (step s i).g50.r1620_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc1 =
      v15632 (step s i) next := by
  apply committed_register_operand_1_reference s i next invariant commit kind aligned zero
  exact decoded.trans (committed_reference_rs1_address s i next commit used).symm

#print axioms committed_register_operand_1_decoded

/-- Connect an instruction-field decoder invariant to the actual reference read port. -/
theorem committed_register_operand_2_decoded (s : State) (i next : Inputs)
    (invariant : RegisterOperand2Aligned s) (commit : v9 (step s i) next = 1)
    (kind : s.g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = 0)
    (aligned : ArchitecturalRegistersAligned (step s i)) (zero : ReferenceZero (step s i))
    (used : referenceUsesRs2 (step s i) next = true)
    (decoded : s.g48.r1556_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc2 =
      BitVec.extractLsb' 20 5 s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (step s i).g50.r1621_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc2 =
      v15394 (step s i) next := by
  apply committed_register_operand_2_reference s i next invariant commit kind aligned zero
  exact decoded.trans (committed_reference_rs2_address s i next commit used).symm

#print axioms committed_register_operand_2_decoded


/-- Discharge the DUT source-address premise using the pipeline decode invariant. -/
theorem committed_register_operand_1_from_decode (s : State) (i next : Inputs)
    (invariant : RegisterOperand1Aligned s) (decode : ExecuteSource1Decoded s)
    (commit : v9 (step s i) next = 1)
    (kind : s.g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = 0)
    (aligned : ArchitecturalRegistersAligned (step s i)) (zero : ReferenceZero (step s i))
    (used : referenceUsesRs1 (step s i) next = true)
    (notLui : BitVec.extractLsb' 0 7 s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr ≠ 55) :
    (step s i).g50.r1620_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc1 =
      v15632 (step s i) next := by
  apply committed_register_operand_1_decoded s i next invariant commit kind aligned zero used
  apply decode (commit_requires_execute_valid s i next commit) kind
  exact fun _ => notLui

#print axioms committed_register_operand_1_from_decode

/-- Discharge the DUT source-address premise using the pipeline decode invariant. -/
theorem committed_register_operand_2_from_decode (s : State) (i next : Inputs)
    (invariant : RegisterOperand2Aligned s) (decode : ExecuteSource2Decoded s)
    (commit : v9 (step s i) next = 1)
    (kind : s.g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = 0)
    (aligned : ArchitecturalRegistersAligned (step s i)) (zero : ReferenceZero (step s i))
    (used : referenceUsesRs2 (step s i) next = true) :
    (step s i).g50.r1621_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc2 =
      v15394 (step s i) next := by
  apply committed_register_operand_2_decoded s i next invariant commit kind aligned zero used
  apply decode (commit_requires_execute_valid s i next commit) kind
  intro impossible; contradiction

#print axioms committed_register_operand_2_from_decode

end NutShellProofs
