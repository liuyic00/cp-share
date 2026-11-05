import Proofs.CommittedPC32
import Proofs.BranchTargetCorrespondence
namespace NutShellProofs
open nNutCore

theorem extend_operand_eq_signExtend (pc : BitVec 39) :
    extendOperandPC pc = pc.signExtend 64 := by
  exact sign_extend_replication pc 25

theorem extend_operand_low39_signed_range (value : BitVec 64)
    (lower : -(2^38 : Int) ≤ value.toInt)
    (upper : value.toInt < (2^38 : Int)) :
    extendOperandPC (BitVec.extractLsb' 0 39 value) = value := by
  rw [extend_operand_eq_signExtend,
    ← BitVec.setWidth_eq_extractLsb' (by decide : 39 ≤ 64),
    ← BitVec.signExtend_eq_setWidth_of_le value (by decide : 39 ≤ 64)]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide : 39 ≤ 64),
    BitVec.toInt_signExtend_eq_toInt_bmod_of_le value (by decide : 39 ≤ 64)]
  exact Int.bmod_eq_of_le (by simpa using lower) (by simpa using upper)

theorem pc32_short_signed_target (pc : BitVec 39) (offset : BitVec 13)
    (high : BitVec.extractLsb' 32 7 pc = 0) :
    extendOperandPC (BitVec.extractLsb' 0 39 (extendOperandPC pc + offset.signExtend 64)) =
      extendOperandPC pc + offset.signExtend 64 := by
  have bound := pc32_toNat_bound pc high
  have pcInt : pc.toInt = (pc.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  have lo := BitVec.le_toInt offset
  have hi := BitVec.toInt_lt (x := offset)
  have sum : (extendOperandPC pc + offset.signExtend 64).toInt = (pc.toNat : Int) + offset.toInt := by
    rw [extend_operand_eq_signExtend, BitVec.toInt_add,
      BitVec.toInt_signExtend_of_le (by decide : 39 ≤ 64),
      BitVec.toInt_signExtend_of_le (by decide : 13 ≤ 64), pcInt]
    apply Int.bmod_eq_of_le <;> simp at * <;> omega
  apply extend_operand_low39_signed_range <;> rw [sum] <;> simp at * <;> omega

#print axioms pc32_short_signed_target

theorem branch_reference_target_full_width (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (matched : IsBranch operation (EXUPair (run initial inputs (t + 1))).1)
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    extendOperandPC (BitVec.extractLsb' 0 39
      (referenceBranchTarget operation (run initial inputs (t + 2)) (inputs (t + 2)))) =
      referenceBranchTarget operation (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have pcs := committed_operand_pc_from_task10 _ _ _ currentReset commit pc
  have imm := committed_reference_branch_immediate _ _ _ operation commit matched
  have high := (temporary_pc32_instruction_pipeline initial inputs reset restriction t).2.2
    (commit_requires_execute_valid _ _ _ commit)
  change extendOperandPC (EXUPair (run initial inputs (t + 1))).2 =
    v16457 (run initial inputs (t + 2)) (inputs (t + 2)) at pcs
  change v16164 (run initial inputs (t + 2)) (inputs (t + 2)) = _ at imm
  rw [reference_branch_target, ← pcs, imm]
  exact pc32_short_signed_target _ _ high

#print axioms branch_reference_target_full_width
end NutShellProofs
