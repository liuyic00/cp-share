import Proofs.JumpRegisterStep
namespace NutShellProofs
open nNutCore

/-- Jump preservation retains the current architectural and PC induction hypotheses. -/
theorem jump_registers_aligned_run_step (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : JumpOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump operation (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    ArchitecturalRegistersAligned (run initial inputs (t + 3)) := by
  have mask : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&&
      operation.mask.setWidth 32 = operation.encoding.setWidth 32 := by
    have instruction := committed_reference_instruction _ _ _ commit
    change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
      BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
    rw [instruction]
    exact jump_match_low32 operation _ matched
  have targetAligned : (match operation with
      | .jal => v16484 (run initial inputs (t + 2)) (inputs (t + 2))
      | .jalr => v16454 (run initial inputs (t + 2)) (inputs (t + 2))) = 1 := by
    cases operation with
    | jal =>
      exact reference_jump_jal_alignment _ _
        (jal_reference_sum_aligned_run initial inputs reset t environment currentReset commit unit matched pc)
    | jalr =>
      exact reference_jump_jalr_alignment _ _
        (jalr_reference_sum_aligned_run initial inputs reset t environment commit unit matched aligned)
  have write := writeback_jump_enabled_run initial inputs reset t operation commit unit matched
  have destination := committed_jump_destination_agrees _ _ _ operation
    (destination1_decode_run initial inputs reset t).2 commit write matched
  exact jump_registers_aligned_step _ _ operation currentReset commit mask targetAligned aligned destination write
    (jump_writeback_reference_pc_plus_four_run initial inputs reset t operation currentReset commit unit matched pc)
#print axioms jump_registers_aligned_run_step
end NutShellProofs
