import Proofs.AluResults
import Proofs.CommittedRegisterOperands
namespace NutShellProofs
open nNutCore

theorem execute_register_operand_1_reference (s : State) (i next : Inputs)
    (invariant : RegisterOperand1Aligned s) (decode : ExecuteSource1Decoded s)
    (commit : v9 (step s i) next = 1)
    (kind : s.g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = 0)
    (aligned : ArchitecturalRegistersAligned (step s i)) (zero : ReferenceZero (step s i))
    (used : referenceUsesRs1 (step s i) next = true)
    (notLui : BitVec.extractLsb' 0 7 s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr ≠ 55) :
    v12148 s i = v15632 (step s i) next := by
  have valid := commit_requires_execute_valid s i next commit
  obtain ⟨reset, flush⟩ := next_commit_controls s i next commit
  have operand := invariant i next valid kind reset flush
  have captured := committed_register_operand_1_dut s i next invariant commit kind
  have reference := committed_register_operand_1_from_decode s i next invariant decode commit kind aligned zero used notLui
  exact operand.trans (captured.symm.trans reference)

theorem execute_register_operand_2_reference (s : State) (i next : Inputs)
    (invariant : RegisterOperand2Aligned s) (decode : ExecuteSource2Decoded s)
    (commit : v9 (step s i) next = 1)
    (kind : s.g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = 0)
    (aligned : ArchitecturalRegistersAligned (step s i)) (zero : ReferenceZero (step s i))
    (used : referenceUsesRs2 (step s i) next = true) :
    v12150 s i = v15394 (step s i) next := by
  have valid := commit_requires_execute_valid s i next commit
  obtain ⟨reset, flush⟩ := next_commit_controls s i next commit
  have operand := invariant i next valid kind reset flush
  have captured := committed_register_operand_2_dut s i next invariant commit kind
  have reference := committed_register_operand_2_from_decode s i next invariant decode commit kind aligned zero used
  exact operand.trans (captured.symm.trans reference)

#print axioms execute_register_operand_1_reference
#print axioms execute_register_operand_2_reference
/-- The actual ALU inputs correspond to the reference reads after older writeback.
The reset-to-run invariants are supplied here, rather than assumed by callers. -/
theorem execute_register_operands_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (kind1 : (run initial inputs (t + 1)).g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = 0)
    (kind2 : (run initial inputs (t + 1)).g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = 0)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (used1 : referenceUsesRs1 (run initial inputs (t + 2)) (inputs (t + 2)) = true)
    (used2 : referenceUsesRs2 (run initial inputs (t + 2)) (inputs (t + 2)) = true)
    (notLui : BitVec.extractLsb' 0 7 (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr ≠ 55) :
    v12148 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v15632 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    v12150 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v15394 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  constructor
  · exact execute_register_operand_1_reference _ _ _
      (register_operand_1_run initial inputs reset t)
      (source1_decode_run initial inputs reset t).2 commit kind1 aligned
      (reference_zero_run initial inputs reset (t + 1)) used1 notLui
  · exact execute_register_operand_2_reference _ _ _
      (register_operand_2_run initial inputs reset t)
      (source2_decode_run initial inputs reset t).2 commit kind2 aligned
      (reference_zero_run initial inputs reset (t + 1)) used2

#print axioms execute_register_operands_run
end NutShellProofs
