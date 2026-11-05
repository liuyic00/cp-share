import Proofs.ReferenceJumpOperands
import Proofs.AuipcCorrespondence
namespace NutShellProofs
open nNutCore

theorem clear_bit_zero_of_word_aligned (value : BitVec 64)
    (aligned : BitVec.extractLsb' 0 2 value = 0) :
    (BitVec.extractLsb' 1 63 value ++ (0 : BitVec 1)) = value := by
  have zero := congrArg (fun x : BitVec 2 => x.getLsbD 0) aligned
  simp at zero
  apply BitVec.eq_of_getLsbD_eq
  intro bit inRange
  by_cases first : bit = 0
  · subst bit
    simpa only [BitVec.getLsbD_append, BitVec.getLsbD_zero, show (0 < 1) by decide, ↓reduceIte] using zero.symm
  · by_cases bound : bit < 64
    · have positive : ¬bit < 1 := by omega
      have upper : bit - 1 < 63 := by omega
      have index : 1 + (bit - 1) = bit := by omega
      rw [BitVec.getLsbD_append]
      simp only [positive, ↓reduceIte]
      rw [BitVec.getLsbD_extractLsb']
      simp only [upper, decide_true, Bool.true_and, index]
    · have high : 64 ≤ bit := by omega
      simp [BitVec.getLsbD_of_ge _ _ high]

theorem reference_jal_target_sum (s : State) (i : Inputs) :
    v23598 s i = v16457 s i + v16164 s i := by
  simp [v23598, v23597, v23595, v23596,
    low_add _ _ (by decide : 64 ≤ 65),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64)]

theorem reference_jalr_target_sum (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 (v15632 s i + v16164 s i) = 0) :
    v23594 s i = v15632 s i + v16164 s i := by
  have sum : v23592 s i = v15632 s i + v16164 s i := by
    simp [v23592, v23591, v23589, v23590,
      low_add _ _ (by decide : 64 ≤ 65),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64)]
  simp only [v23594, v23593, sum, v24]
  exact clear_bit_zero_of_word_aligned _ aligned

theorem jalr_reference_sum_aligned_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jalr (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    BitVec.extractLsb' 0 2 (v15632 (run initial inputs (t + 2)) (inputs (t + 2)) +
      v16164 (run initial inputs (t + 2)) (inputs (t + 2))) = 0 := by
  have target := jump_target_alignment_run initial inputs reset t .jalr environment
    (next_commit_controls _ _ _ commit).1 (commit_requires_execute_valid _ _ _ commit) unit matched
  rw [jalr_operand_matches_reference_run initial inputs reset t commit unit matched aligned,
    jump_immediate_matches_reference_run initial inputs reset t .jalr commit unit matched] at target
  exact target

theorem jalr_target_matches_reference_node_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jalr (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v12212 (run initial inputs (t + 1)) (inputs (t + 1)) =
      BitVec.extractLsb' 0 39 (v23594 (run initial inputs (t + 2)) (inputs (t + 2))) := by
  rw [reference_jalr_target_sum _ _
    (jalr_reference_sum_aligned_run initial inputs reset t environment commit unit matched aligned)]
  exact jalr_target_reference_operands_run initial inputs reset t commit unit matched aligned

#print axioms clear_bit_zero_of_word_aligned
#print axioms jalr_target_matches_reference_node_run

theorem jal_target_matches_reference_node_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jal (EXUPair (run initial inputs (t + 1))).1)
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    v12212 (run initial inputs (t + 1)) (inputs (t + 1)) =
      BitVec.extractLsb' 0 39 (v23598 (run initial inputs (t + 2)) (inputs (t + 2))) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have pcs := committed_operand_pc_from_task10 _ _ _ currentReset commit pc
  rw [jump_target_run initial inputs reset t .jal valid unit matched,
    jal_pc_operand_run initial inputs reset t valid unit matched,
    jump_immediate_matches_reference_run initial inputs reset t .jal commit unit matched,
    reference_jal_target_sum]
  exact congrArg (fun address : BitVec 64 => BitVec.extractLsb' 0 39
    (address + v16164 (run initial inputs (t + 2)) (inputs (t + 2)))) pcs

#print axioms jal_target_matches_reference_node_run
end NutShellProofs
