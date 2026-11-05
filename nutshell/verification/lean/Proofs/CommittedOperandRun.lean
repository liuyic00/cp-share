import Proofs.CommittedRegisterOperands
namespace NutShellProofs
open nNutCore

/-- Actual committed operand after reset; only architectural and instruction-use premises remain. -/
theorem committed_register_operand_1_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (kind : (run initial inputs (t + 1)).g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = 0)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (used : referenceUsesRs1 (run initial inputs (t + 2)) (inputs (t + 2)) = true)
    (notLui : BitVec.extractLsb' 0 7 (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr ≠ 55) :
    (run initial inputs (t + 2)).g50.r1620_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc1 =
      v15632 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  exact committed_register_operand_1_from_decode _ _ _
    (register_operand_1_run initial inputs reset t)
    (source1_decode_run initial inputs reset t).2 commit kind aligned
    (reference_zero_run initial inputs reset (t + 1)) used notLui

#print axioms committed_register_operand_1_run


/-- Actual committed operand after reset; only architectural and instruction-use premises remain. -/
theorem committed_register_operand_2_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (kind : (run initial inputs (t + 1)).g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = 0)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (used : referenceUsesRs2 (run initial inputs (t + 2)) (inputs (t + 2)) = true) :
    (run initial inputs (t + 2)).g50.r1621_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fdata_5Fsrc2 =
      v15394 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  exact committed_register_operand_2_from_decode _ _ _
    (register_operand_2_run initial inputs reset t)
    (source2_decode_run initial inputs reset t).2 commit kind aligned
    (reference_zero_run initial inputs reset (t + 1)) used

#print axioms committed_register_operand_2_run

end NutShellProofs
