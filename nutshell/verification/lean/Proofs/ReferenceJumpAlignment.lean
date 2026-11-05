import Proofs.ReferenceJumpControl
namespace NutShellProofs
open nNutCore
theorem reference_jump_jal_alignment (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 (v16457 s i + v16164 s i) = 0) :
    v16484 s i = 1 := by
  have target : v16470 s i = v16457 s i + v16164 s i := by
    exact reference_jal_target_sum s i
  have low : BitVec.extractLsb' 0 1 (v16457 s i + v16164 s i) = 0 := by
    have h := congrArg (BitVec.extractLsb' 0 1) aligned
    simpa only [low_low _ (by decide : 1 ≤ 2)] using h
  rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb' 2 1 (v16429 s i)) with c | c
  all_goals simp [v16462, v16463, v16464, v16465, v16466, v16471, v16472, v16473, v16474, v16475, v16476, v16477, v16478, v16479, v16480, v16481, v16482, v16483, v16484, target, aligned, low, c, v110, v24, v9721, v2750]
#print axioms reference_jump_jal_alignment

theorem reference_jump_jalr_alignment (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 (v15632 s i + v16164 s i) = 0) :
    v16454 s i = 1 := by
  have target : v16440 s i = v15632 s i + v16164 s i := by
    exact reference_jalr_target_sum s i aligned
  have low : BitVec.extractLsb' 0 1 (v15632 s i + v16164 s i) = 0 := by
    have h := congrArg (BitVec.extractLsb' 0 1) aligned
    simpa only [low_low _ (by decide : 1 ≤ 2)] using h
  rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb' 2 1 (v16429 s i)) with c | c
  all_goals simp [v16430, v16431, v16432, v16433, v16434, v16441, v16442, v16443, v16444, v16445, v16446, v16447, v16448, v16449, v16450, v16451, v16452, v16453, v16454, target, aligned, low, c, v110, v24, v9721, v2750]
#print axioms reference_jump_jalr_alignment


theorem jalr_reference_control_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jalr (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v23620 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v23594 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    v23529 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 ∧
    v23407 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
  have mask : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (28799 : BitVec 32) = 103 := by
    have instruction := committed_reference_instruction _ _ _ commit
    change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) = BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
    rw [instruction]
    exact jump_match_low32 .jalr _ matched
  have ok := reference_jump_jalr_alignment _ _
    (jalr_reference_sum_aligned_run initial inputs reset t environment commit unit matched aligned)
  exact ⟨reference_jump_jalr_selection _ _ mask ok,
    reference_jump_jalr_redirect _ _ mask ok, reference_jump_jalr_no_exception _ _ mask ok⟩

#print axioms jalr_reference_control_run
theorem jal_reference_sum_aligned_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jal (EXUPair (run initial inputs (t + 1))).1)
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    BitVec.extractLsb' 0 2 (v16457 (run initial inputs (t + 2)) (inputs (t + 2)) +
      v16164 (run initial inputs (t + 2)) (inputs (t + 2))) = 0 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have target := jump_target_alignment_run initial inputs reset t .jal environment
    (next_commit_controls _ _ _ commit).1 valid unit matched
  have pcs := committed_operand_pc_from_task10 _ _ _ currentReset commit pc
  rw [jal_pc_operand_run initial inputs reset t valid unit matched,
    jump_immediate_matches_reference_run initial inputs reset t .jal commit unit matched] at target
  change extendOperandPC (EXUPair (run initial inputs (t + 1))).2 =
    v16457 (run initial inputs (t + 2)) (inputs (t + 2)) at pcs
  rw [pcs] at target
  exact target
#print axioms jal_reference_sum_aligned_run
end NutShellProofs
