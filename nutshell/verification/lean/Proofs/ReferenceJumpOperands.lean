import Proofs.CommittedJumpImmediate
namespace NutShellProofs
open nNutCore

theorem committed_reference_jalr_uses_rs1 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (matched : IsJump .jalr (EXUPair s).1) :
    referenceUsesRs1 (step s i) next = true := by
  apply reference_uses_rs1_of_jalr_match _ _ commit
  have low := jump_match_low32 .jalr (EXUPair s).1 matched
  have eq : v14575 (step s i) next &&& (28799 : BitVec 32) = 103 := by
    rw [committed_reference_instruction s i next commit]
    exact low
  simp [v14901, v14898, v14900, v14899]
  exact eq.symm

theorem jalr_operand_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jalr (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v12148 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v15632 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨_, kind1, _, _, _⟩ := (jump_decode_run initial inputs reset t).2 valid .jalr matched unit
  have opcode := opcode_of_mask _ (JumpOp.mask .jalr) (JumpOp.encoding .jalr) (by decide) matched.symm
  have notLui : BitVec.extractLsb' 0 7 (EXUPair (run initial inputs (t + 1))).1 ≠ 55 := by
    rw [opcode]; decide
  exact execute_register_operand_1_reference _ _ _
    (register_operand_1_run initial inputs reset t)
    (source1_decode_run initial inputs reset t).2 commit kind1 aligned
    (reference_zero_run initial inputs reset (t + 1))
    (committed_reference_jalr_uses_rs1 _ _ _ commit matched) notLui

theorem jalr_target_reference_operands_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jalr (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v12212 (run initial inputs (t + 1)) (inputs (t + 1)) =
      BitVec.extractLsb' 0 39 (v15632 (run initial inputs (t + 2)) (inputs (t + 2)) +
        v16164 (run initial inputs (t + 2)) (inputs (t + 2))) := by
  rw [jump_target_run initial inputs reset t .jalr (commit_requires_execute_valid _ _ _ commit) unit matched,
    jalr_operand_matches_reference_run initial inputs reset t commit unit matched aligned,
    jump_immediate_matches_reference_run initial inputs reset t .jalr commit unit matched]

#print axioms jalr_operand_matches_reference_run
#print axioms jalr_target_reference_operands_run
end NutShellProofs
