import Proofs.JumpTarget
import Proofs.ImmediateArithmetic
namespace NutShellProofs
open nNutCore

theorem jump_immediate_operand_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : JumpOp)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump operation (EXUPair (run initial inputs (t + 1))).1) :
    v12150 (run initial inputs (t + 1)) (inputs (t + 1)) =
      jumpImmediate operation (EXUPair (run initial inputs (t + 1))).1 := by
  obtain ⟨_, _, kind2, imm, _⟩ := (jump_decode_run initial inputs reset t).2 valid operation matched unit
  exact ((nonregister_operand_2_run initial inputs reset t) valid kind2).trans imm

theorem jal_pc_operand_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jal (EXUPair (run initial inputs (t + 1))).1) :
    v12148 (run initial inputs (t + 1)) (inputs (t + 1)) =
      extendOperandPC (EXUPair (run initial inputs (t + 1))).2 := by
  obtain ⟨_, kind1, _, _, _⟩ := (jump_decode_run initial inputs reset t).2 valid .jal matched unit
  exact (nonregister_operand_1_run initial inputs reset t) valid kind1

theorem jal_target_pc_immediate_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jal (EXUPair (run initial inputs (t + 1))).1) :
    v12212 (run initial inputs (t + 1)) (inputs (t + 1)) =
      (EXUPair (run initial inputs (t + 1))).2 +
      BitVec.extractLsb' 0 39 (immediateJ (EXUPair (run initial inputs (t + 1))).1) := by
  rw [jump_target_run initial inputs reset t .jal valid unit matched,
    jal_pc_operand_run initial inputs reset t valid unit matched,
    jump_immediate_operand_run initial inputs reset t .jal valid unit matched]
  simp only [jumpImmediate, low_add _ _ (by decide : 39 ≤ 64), extendOperandPC,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 39), BitVec.extractLsb'_eq_self]

theorem jalr_target_register_immediate_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jalr (EXUPair (run initial inputs (t + 1))).1) :
    v12212 (run initial inputs (t + 1)) (inputs (t + 1)) =
      BitVec.extractLsb' 0 39
        (v12148 (run initial inputs (t + 1)) (inputs (t + 1)) +
          immediateI (EXUPair (run initial inputs (t + 1))).1) := by
  rw [jump_target_run initial inputs reset t .jalr valid unit matched,
    jump_immediate_operand_run initial inputs reset t .jalr valid unit matched]
  rfl

#print axioms jump_immediate_operand_run
#print axioms jal_target_pc_immediate_run
#print axioms jalr_target_register_immediate_run

theorem jalr_register_operand_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jalr (EXUPair (run initial inputs (t + 1))).1) :
    v12148 (run initial inputs (t + 1)) (inputs (t + 1)) =
      dutRead.v25201 (run initial inputs (t + 2)) (inputs (t + 2))
        (BitVec.extractLsb' 15 5 (EXUPair (run initial inputs (t + 1))).1) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨_, kind1, _, _, _⟩ := (jump_decode_run initial inputs reset t).2 valid .jalr matched unit
  obtain ⟨noReset, noFlush⟩ := next_commit_controls _ _ _ commit
  have opcode := opcode_of_mask _ (JumpOp.mask .jalr) (JumpOp.encoding .jalr) (by decide) matched.symm
  have notLui : BitVec.extractLsb' 0 7 (EXUPair (run initial inputs (t + 1))).1 ≠ 55 := by
    rw [opcode]; decide
  have address := (source1_decode_run initial inputs reset t).2 valid kind1 (fun _ => notLui)
  have operand := register_operand_1_run initial inputs reset t
    (inputs (t + 1)) (inputs (t + 2)) valid kind1 noReset noFlush
  change v12148 (run initial inputs (t + 1)) (inputs (t + 1)) = _ at operand
  simpa only [address] using operand

#print axioms jalr_register_operand_run
end NutShellProofs
