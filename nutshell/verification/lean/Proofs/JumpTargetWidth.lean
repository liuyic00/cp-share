import Proofs.CommittedPC32
import Proofs.MemoryAddressWidth
import Proofs.ReferenceJumpPC
namespace NutShellProofs
open nNutCore

theorem extend_operand_low39_upper_zero (value : BitVec 64)
    (upper : BitVec.extractLsb' 38 26 value = 0) :
    extendOperandPC (BitVec.extractLsb' 0 39 value) = value := by
  have bound := value.isLt
  have bits := congrArg BitVec.toNat upper
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at bits
  have small : value.toNat < 2^38 := by omega
  have low : (BitVec.extractLsb' 0 39 value).toNat = value.toNat := by
    simp [BitVec.extractLsb'_toNat]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [extend_pc_small _ (by rw [low]; exact small), low]

theorem jalr_reference_target_upper_zero (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jalr (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    BitVec.extractLsb' 38 26 (v23594 (run initial inputs (t + 2)) (inputs (t + 2))) = 0 := by
  have upper := original_memory_address_upper_zero _ _ (environment (t + 1))
    (next_commit_controls _ _ _ commit).1
  rw [lsu_address_sum _ _ (original_assumptions_lsu_idle_run initial inputs reset environment t)] at upper
  have operands := jalr_operand_matches_reference_run initial inputs reset t commit unit matched registers
  have imm := ((jump_decode_run initial inputs reset t).2
    (commit_requires_execute_valid _ _ _ commit) .jalr matched unit).2.2.2.1
  have immediate := imm.trans (committed_reference_jump_immediate _ _ _ .jalr commit matched).symm
  change v11592 (run initial inputs (t + 1)) (inputs (t + 1)) = _ at operands
  change v11595 (run initial inputs (t + 1)) (inputs (t + 1)) = _ at immediate
  rw [operands, immediate] at upper
  rw [reference_jalr_target_sum _ _
    (jalr_reference_sum_aligned_run initial inputs reset t (environment (t + 1)) commit unit matched registers)]
  exact upper


theorem jal_reference_target_upper_zero (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jal (EXUPair (run initial inputs (t + 1))).1)
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    BitVec.extractLsb' 38 26 (v23598 (run initial inputs (t + 2)) (inputs (t + 2))) = 0 := by
  have upper := original_memory_address_upper_zero _ _ (environment (t + 1))
    (next_commit_controls _ _ _ commit).1
  rw [lsu_address_sum _ _ (original_assumptions_lsu_idle_run initial inputs reset environment t)] at upper
  have valid := commit_requires_execute_valid _ _ _ commit
  have operands := (jal_pc_operand_run initial inputs reset t valid unit matched).trans
    (committed_operand_pc_from_task10 _ _ _ currentReset commit pc)
  have imm := ((jump_decode_run initial inputs reset t).2 valid .jal matched unit).2.2.2.1
  have immediate := imm.trans (committed_reference_jump_immediate _ _ _ .jal commit matched).symm
  change v11592 (run initial inputs (t + 1)) (inputs (t + 1)) = _ at operands
  change v11595 (run initial inputs (t + 1)) (inputs (t + 1)) = _ at immediate
  rw [operands, immediate] at upper
  rw [reference_jal_target_sum]
  exact upper

#print axioms jal_reference_target_upper_zero

#print axioms jalr_reference_target_upper_zero
end NutShellProofs
