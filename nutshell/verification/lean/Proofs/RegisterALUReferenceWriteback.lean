import Proofs.RegisterALUWriteback
import Proofs.ReferenceRegisterALU
namespace NutShellProofs
open nNutCore

/-- Both actual reference reads replace the ALU operands under register alignment. -/
theorem writeback_register_alu_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : RegisterALUOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsRegisterALU operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      operation.eval (v15632 (run initial inputs (t + 2)) (inputs (t + 2)))
        (v15394 (run initial inputs (t + 2)) (inputs (t + 2))) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨_, kind1, kind2, _⟩ :=
    (register_alu_decode_run initial inputs reset t).2 valid operation matched unit
  have used1 := committed_reference_register_alu_uses_rs1 _ _ _ operation commit matched
  have used2 := committed_reference_register_alu_uses_rs2 _ _ _ operation commit matched
  obtain ⟨source1, source2⟩ := execute_register_operands_run initial inputs reset t
    commit kind1 kind2 aligned used1 used2 (register_alu_not_lui operation _ matched)
  have result := writeback_register_alu_raw_run initial inputs reset t operation commit unit matched
  simpa only [source1, source2] using result

#print axioms writeback_register_alu_reference_run
end NutShellProofs
