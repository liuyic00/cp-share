import Proofs.InstructionWidth

namespace NutShellProofs
open nNutCore

theorem instruction32_rebuild (x : BitVec 64) (h : Instruction32 x) :
    (0 : BitVec 32) ++ BitVec.extractLsb' 0 32 x = x := by
  obtain ⟨low, rfl⟩ := h
  change (0 : BitVec 32) ++ BitVec.setWidth 32 ((0 : BitVec 32) ++ low) = ((0 : BitVec 32) ++ low)
  rw [BitVec.setWidth_append (x := (0 : BitVec 32)) (y := low) (k := 32)]
  rfl

theorem task_47_from_event_valid (s : State) (i next : Inputs)
    (width : EXUInstruction32 s) (event : TaskHolds 43 (step s i) next) :
    TaskHolds 47 (step s i) next := by
  change decide (v31789 (step s i) next ≠ 1 ∨ v31787 (step s i) next = 1) = true
  apply decide_eq_true
  by_cases enabled : v31789 (step s i) next = 1
  · right
    have eventCheck : v31743 (step s i) next ≠ 1 ∨ v31740 (step s i) next = 1 :=
      of_decide_eq_true event
    have gate : v31743 (step s i) next = 1 := enabled
    have compare := eventCheck.resolve_left (not_not_intro gate)
    have flags : v31736 (step s i) next = v31739 (step s i) next := by
      simpa [v31740] using compare
    have refValid : v31739 (step s i) next = 1 := by
      rcases BitVec.eq_zero_or_eq_one (v31739 (step s i) next) with zero | one
      · have actualZero := flags.trans zero
        simp [v31789, v31741, actualZero, zero] at enabled
      · exact one
    have commit : v9 (step s i) next = 1 := by
      rcases BitVec.eq_zero_or_eq_one (v9 (step s i) next) with zero | one
      · simp [v31739, v31738, v31737, v14560, v14559, v14558, zero, v24] at refValid
      · exact one
    have refException : v23407 (step s i) next = 1 := by
      simpa [v31739, v31738, v31737, v14560, v14559, v14558, commit] using refValid
    have noReset : i.g0.nreset = 0 := by
      rcases BitVec.eq_zero_or_eq_one i.g0.nreset with zero | one
      · exact zero
      · change v25331 s i = 1 at commit
        simp [v25331, v11455, one, v24] at commit
    have valid := commit_requires_execute_valid s i next commit
    have narrow := width valid
    have capture := capture_decode_cf_instr s i next commit
    have rebuilt : v31782 (step s i) next = v11547 s i := by
      simp only [v31782, v11103, v14575, v14560, v14559, v14558, commit,
        ↓reduceIte, v14573, v14572, v14571, v14570, v14569]
      rw [capture]
      exact instruction32_rebuild _ narrow
    have actual : v31781 (step s i) next = v11547 s i := by
      change v14426 s i = v11547 s i
      simp [v14426, v13172, v12103, v11455, noReset, v13425]
    have reference : v31786 (step s i) next = v11547 s i := by
      simp [v31786, v31785, v31784, v14560, v14559, v14558, commit,
        v31783, refException, rebuilt]
    simp [v31787, actual, reference]
  · exact Or.inl enabled

theorem task_47_run_from_event_valid (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (event : TaskHolds 43 (run initial inputs t) (inputs t)) :
    TaskHolds 47 (run initial inputs t) (inputs t) := by
  cases t with
  | zero =>
    change decide (v31789 initial (inputs 0) ≠ 1 ∨ v31787 initial (inputs 0) = 1) = true
    simp [v31789, v31788, v14554, v14553, v11455, v24, reset]
  | succ t =>
    cases t with
    | zero =>
      have actual : v31736 (step initial (inputs 0)) (inputs 1) = 0 := by
        change v14412 initial (inputs 0) = 0
        simp [v14412, v13172, v12103, v11455, v24, reset]
      have commit : v9 (step initial (inputs 0)) (inputs 1) = 0 := by
        change v25331 initial (inputs 0) = 0
        simp [v25331, v11455, v24, reset]
      change decide (v31789 (step initial (inputs 0)) (inputs 1) ≠ 1 ∨ _) = true
      simp [v31789, v31741, actual, v31739, v31738, v31737,
        v14560, v14559, v14558, commit, v24]
    | succ t =>
      exact task_47_from_event_valid _ _ _
        (instruction_width_run initial inputs reset t).2.2 event

#print axioms task_47_run_from_event_valid
#print axioms task_47_from_event_valid
end NutShellProofs
