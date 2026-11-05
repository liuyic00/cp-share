import Proofs.ShiftPipeline
import Proofs.ReferenceShift
import Proofs.ImmediateArithmetic
namespace NutShellProofs
open nNutCore

def ShiftImmediateOp.eval (operation : ShiftImmediateOp) (x y : BitVec 64) : BitVec 64 :=
  match operation with
  | .sll => BitVec.shiftLeft x (BitVec.extractLsb' 0 6 y).toNat
  | .srl => BitVec.ushiftRight x (BitVec.extractLsb' 0 6 y).toNat
  | .sra => BitVec.sshiftRight x (BitVec.extractLsb' 0 6 y).toNat

theorem writeback_shift_raw_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : ShiftImmediateOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsShiftImmediate operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      operation.eval (v12148 (run initial inputs (t + 1)) (inputs (t + 1)))
        (immediateI (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨op, _kind1, kind2, imm, _write⟩ :=
    (shift_decode_run initial inputs reset t).2 valid operation matched unit
  have operand := execute_immediate_operand _ _ _
    (nonregister_operand_2_run initial inputs reset t) commit kind2
  have result : v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      operation.eval (v12148 (run initial inputs (t + 1)) (inputs (t + 1)))
        (v12150 (run initial inputs (t + 1)) (inputs (t + 1))) := by
    cases operation with
    | sll => exact writeback_alu_sll _ _ _ commit unit op
    | srl => exact writeback_alu_srl _ _ _ commit unit op
    | sra => exact writeback_alu_sra _ _ _ commit unit op
  simpa only [operand, imm] using result

theorem writeback_shift_enabled_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : ShiftImmediateOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsShiftImmediate operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11462 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨_, _, _, _, enabled⟩ :=
    (shift_decode_run initial inputs reset t).2 valid operation matched unit
  exact alu_next_writeback_enabled _ _ _ commit unit enabled

#print axioms writeback_shift_raw_run
#print axioms writeback_shift_enabled_run
/-- Actual writeback expressed using the reference source register. Only the
architectural alignment induction premise remains for operand correspondence. -/
theorem writeback_shift_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : ShiftImmediateOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsShiftImmediate operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      operation.eval (v15632 (run initial inputs (t + 2)) (inputs (t + 2)))
        (immediateI (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨_, kind1, _, _, _⟩ :=
    (shift_decode_run initial inputs reset t).2 valid operation matched unit
  have used := committed_reference_shift_uses_rs1 _ _ _ operation commit matched
  have source := execute_register_operand_1_reference _ _ _
    (register_operand_1_run initial inputs reset t) (source1_decode_run initial inputs reset t).2
    commit kind1 aligned (reference_zero_run initial inputs reset (t + 1)) used
    (shift_not_lui operation _ matched)
  have result := writeback_shift_raw_run initial inputs reset t operation commit unit matched
  simpa only [source] using result

#print axioms writeback_shift_reference_run
end NutShellProofs
