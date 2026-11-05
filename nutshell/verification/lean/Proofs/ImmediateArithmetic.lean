import Proofs.NonregisterOperands
import Proofs.AluOperandCorrespondence
namespace NutShellProofs
open nNutCore

theorem execute_immediate_operand (s : State) (i next : Inputs)
    (invariant : NonregisterOperand2 s) (commit : v9 (step s i) next = 1)
    (kind : s.g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = 1) :
    v12150 s i = s.g48.r1566_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fimm :=
  invariant (commit_requires_execute_valid s i next commit) kind

theorem execute_pc_operand (s : State) (i next : Inputs)
    (invariant : NonregisterOperand1 s) (commit : v9 (step s i) next = 1)
    (kind : s.g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = 1) :
    v12148 s i = extendOperandPC s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc :=
  invariant (commit_requires_execute_valid s i next commit) kind

/-- Actual PC-relative addition. The instruction's decoded immediate is still explicit. -/
theorem writeback_pc_immediate_add_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (op : v28 (run initial inputs (t + 1)) (inputs (t + 1)) = 64)
    (kind1 : (run initial inputs (t + 1)).g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = 1)
    (kind2 : (run initial inputs (t + 1)).g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = 1) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      extendOperandPC (run initial inputs (t + 1)).g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc +
      (run initial inputs (t + 1)).g48.r1566_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fimm := by
  have pc := execute_pc_operand _ _ _ (nonregister_operand_1_run initial inputs reset t) commit kind1
  have imm := execute_immediate_operand _ _ _ (nonregister_operand_2_run initial inputs reset t) commit kind2
  have result := writeback_alu_add _ _ _ commit unit op
  simpa only [pc, imm] using result

/-- Register/immediate addition after connecting the actual register source to the reference. -/
theorem writeback_register_immediate_add_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (op : v28 (run initial inputs (t + 1)) (inputs (t + 1)) = 64)
    (kind1 : (run initial inputs (t + 1)).g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = 0)
    (kind2 : (run initial inputs (t + 1)).g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = 1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (used : referenceUsesRs1 (run initial inputs (t + 2)) (inputs (t + 2)) = true)
    (notLui : BitVec.extractLsb' 0 7 (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr ≠ 55) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v15632 (run initial inputs (t + 2)) (inputs (t + 2)) +
      (run initial inputs (t + 1)).g48.r1566_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fimm := by
  have source := execute_register_operand_1_reference _ _ _
    (register_operand_1_run initial inputs reset t) (source1_decode_run initial inputs reset t).2
    commit kind1 aligned (reference_zero_run initial inputs reset (t + 1)) used notLui
  have imm := execute_immediate_operand _ _ _ (nonregister_operand_2_run initial inputs reset t) commit kind2
  have result := writeback_alu_add _ _ _ commit unit op
  simpa only [source, imm] using result

#print axioms writeback_pc_immediate_add_run
#print axioms writeback_register_immediate_add_run
end NutShellProofs
