import Proofs.JumpLink
namespace NutShellProofs
open nNutCore

theorem jump_control_target_bits (operation : JumpOp) (instr : BitVec 64) :
    BitVec.extractLsb' 3 1 (jumpControl operation instr) = 1 ∧
    BitVec.extractLsb' 6 1 (jumpControl operation instr) = 1 := by
  cases operation <;> simp only [jumpControl]
  all_goals repeat' first | split | decide

theorem jump_target_actual (s : State) (i : Inputs) (operation : JumpOp)
    (op : v28 s i = jumpControl operation (EXUPair s).1) :
    v12212 s i = BitVec.extractLsb' 0 39 (v12148 s i + v12150 s i) ∧
    v12211 s i = BitVec.extractLsb' 0 39 (v12148 s i + v12150 s i) := by
  have bits := jump_control_target_bits operation (EXUPair s).1
  have jump : v12182 s i = 0 := by
    simp [v12182, v12181, v12141, op, bits.1, v24]
  have add : v12159 s i = 0 := by
    simp [v12159, v12158, v12141, op, bits.2, v24]
  have target : v12211 s i = BitVec.extractLsb' 0 39 (v12148 s i + v12150 s i) := by
    simp [v12211, v12210, jump, v12169, v12168, v12165, v12164,
      v12157, v12163, v12162, v12161, add, v4051, v24, v12167, v12166,
      low_low _ (by decide : 39 ≤ 65),
      low_add _ _ (by decide : 39 ≤ 66), low_add _ _ (by decide : 39 ≤ 65),
      low_add _ _ (by decide : 39 ≤ 64),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 65),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 64)]
  exact ⟨by simp [v12212, v12190, jump, target], target⟩

theorem original_jump_alignment_assumption (s : State) (i : Inputs) (operation : JumpOp)
    (environment : assumes s i) (reset : i.g0.nreset = 0)
    (op : v28 s i = jumpControl operation (EXUPair s).1) :
    BitVec.extractLsb' 0 2 (v12211 s i) = 0 := by
  have all : (assumptionChecks0 s i).all id = true := environment
  simp only [assumptionChecks0, List.all_cons, List.all_nil, Bool.and_eq_true,
    Bool.true_and, Bool.and_true] at all
  have check : v31810 s i ≠ 1 ∨ v31809 s i = 1 := of_decide_eq_true all.2.2.1
  have gate : v31810 s i = 1 := by simp [v31810, v24, reset]
  have enabled := check.resolve_left (not_not_intro gate)
  have jumpCheck : v31805 s i = 1 := by
    change v31795 s i &&& v31805 s i = 1 at enabled
    rcases BitVec.eq_zero_or_eq_one (v31805 s i) with idle | active
    · simp [idle] at enabled
    · exact active
  have bit3 := (jump_control_target_bits operation (EXUPair s).1).1
  have bit4 := jump_control_branch_bit operation (EXUPair s).1
  simpa [v31805, v31801, v31800, v31796, v31799, v31798, v31797,
    v12141, op, bit3, bit4, v24, v31804, v31802, v31803] using jumpCheck

theorem jump_target_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : JumpOp)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump operation (EXUPair (run initial inputs (t + 1))).1) :
    v12212 (run initial inputs (t + 1)) (inputs (t + 1)) =
      BitVec.extractLsb' 0 39 (v12148 (run initial inputs (t + 1)) (inputs (t + 1)) +
        v12150 (run initial inputs (t + 1)) (inputs (t + 1))) := by
  exact (jump_target_actual _ _ operation
    ((jump_decode_run initial inputs reset t).2 valid operation matched unit).1).1

#print axioms jump_target_actual
#print axioms original_jump_alignment_assumption
#print axioms jump_target_run

theorem jump_target_alignment_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : JumpOp)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump operation (EXUPair (run initial inputs (t + 1))).1) :
    BitVec.extractLsb' 0 2
      (v12148 (run initial inputs (t + 1)) (inputs (t + 1)) +
        v12150 (run initial inputs (t + 1)) (inputs (t + 1))) = 0 := by
  have op := ((jump_decode_run initial inputs reset t).2 valid operation matched unit).1
  have aligned := original_jump_alignment_assumption _ _ operation environment currentReset op
  rw [(jump_target_actual _ _ operation op).2] at aligned
  simpa only [low_low _ (by decide : 2 ≤ 39)] using aligned

#print axioms jump_target_alignment_run
end NutShellProofs
