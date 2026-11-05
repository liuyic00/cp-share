import Proofs.CommittedLuiOperand
import Proofs.UpperPipeline
import Proofs.ImmediateArithmetic
namespace NutShellProofs
open nNutCore

theorem writeback_upper_raw_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : UpperImmediateOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsUpperImmediate operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      (· + ·) (v12148 (run initial inputs (t + 1)) (inputs (t + 1)))
        (immediateU (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨op, _kind1, kind2, imm, _write⟩ :=
    (upper_decode_run initial inputs reset t).2 valid operation matched unit
  have operand := execute_immediate_operand _ _ _
    (nonregister_operand_2_run initial inputs reset t) commit kind2
  have result : v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      (· + ·) (v12148 (run initial inputs (t + 1)) (inputs (t + 1)))
        (v12150 (run initial inputs (t + 1)) (inputs (t + 1))) := by
    exact writeback_alu_add _ _ _ commit unit op
  simpa only [operand, imm] using result

theorem writeback_upper_enabled_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : UpperImmediateOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsUpperImmediate operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11462 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨_, _, _, _, enabled⟩ :=
    (upper_decode_run initial inputs reset t).2 valid operation matched unit
  exact alu_next_writeback_enabled _ _ _ commit unit enabled


#print axioms writeback_upper_raw_run
#print axioms writeback_upper_enabled_run
theorem writeback_auipc_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsUpperImmediate .auipc (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      extendOperandPC (run initial inputs (t + 1)).g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc +
      immediateU (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨op, kind1, kind2, imm, _⟩ :=
    (upper_decode_run initial inputs reset t).2 valid .auipc matched unit
  have result := writeback_pc_immediate_add_run initial inputs reset t commit unit op kind1 kind2
  simpa only [imm] using result

#print axioms writeback_auipc_run
theorem writeback_lui_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsUpperImmediate .lui (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      immediateU (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨_, kind1, _, _, _⟩ := (upper_decode_run initial inputs reset t).2 valid .lui matched unit
  have opcode := opcode_of_mask _ (UpperImmediateOp.mask .lui) (UpperImmediateOp.encoding .lui)
    (by decide) matched.symm
  have address := (lui_source1_decode_run initial inputs reset t).2 valid opcode
  obtain ⟨clearReset, flush⟩ := next_commit_controls _ _ _ commit
  have operand := register_operand_1_run initial inputs reset t
    (inputs (t + 1)) (inputs (t + 2)) valid kind1 clearReset flush
  have zero : v12148 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
    rw [address, dutRead.read_0] at operand
    exact operand
  have result := writeback_upper_raw_run initial inputs reset t .lui commit unit matched
  dsimp only at result
  simpa [zero] using result

#print axioms writeback_lui_run
end NutShellProofs
