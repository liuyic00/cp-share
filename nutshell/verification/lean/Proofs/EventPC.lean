import Proofs.EventInstruction
namespace NutShellProofs
open nNutCore

private theorem reference_event_pc (s : State) (i : Inputs)
    (commit : v9 s i = 1) (event : v23407 s i = 1) : v31774 s i = v31358 s i := by
  simp only [v31774, v31773, v31772, v14560, v14559, v14558, commit,
    v31771, event, ↓reduceIte]
  rfl

theorem task_46_from_event_and_pc (s : State) (i next : Inputs)
    (pc : TaskHolds 10 (step s i) next) (event : TaskHolds 43 (step s i) next) :
    TaskHolds 46 (step s i) next := by
  change decide (v31777 (step s i) next ≠ 1 ∨ v31775 (step s i) next = 1) = true
  apply decide_eq_true
  by_cases enabled : v31777 (step s i) next = 1
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
        simp [v31777, v31741, actualZero, zero] at enabled
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
    have nextNoReset : next.g0.nreset = 0 := by
      rcases BitVec.eq_zero_or_eq_one next.g0.nreset with zero | one
      · exact zero
      · simp [v31777, v31776, v14554, v14553, v11455, v24, one] at enabled
    have pcCheck : v31361 (step s i) next ≠ 1 ∨ v31359 (step s i) next = 1 :=
      of_decide_eq_true pc
    have pcGate : v31361 (step s i) next = 1 := by
      simp [v31361, v14558, commit, v31360, v14554, v14553, v11455, v24, nextNoReset]
    have pcCompare := pcCheck.resolve_left (not_not_intro pcGate)
    have pcs : v31357 (step s i) next = v31358 (step s i) next := by
      simpa [v31359] using pcCompare
    have capture := capture_decode_cf_pc s i next commit
    have capturedPC : v31357 (step s i) next = v14423 s i := by
      exact congrArg (fun pc : BitVec 39 =>
        (if BitVec.extractLsb' 38 1 pc = 1 then BitVec.ofNat 25 33554431
         else BitVec.ofNat 25 0) ++ pc) capture
    have actual : v31770 (step s i) next = v14423 s i := by
      change v14424 s i = v14423 s i
      simp [v14424, v13172, v12103, v11455, noReset]
    have reference := reference_event_pc (step s i) next commit refException
    have same : v31770 (step s i) next = v31774 (step s i) next :=
      actual.trans (capturedPC.symm.trans (pcs.trans reference.symm))
    simp only [v31775, same, ↓reduceIte]
  · exact Or.inl enabled

theorem task_46_run_from_event_and_pc (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (event : TaskHolds 43 (run initial inputs t) (inputs t))
    (pc : TaskHolds 10 (run initial inputs t) (inputs t)) :
    TaskHolds 46 (run initial inputs t) (inputs t) := by
  cases t with
  | zero =>
    change decide (v31777 initial (inputs 0) ≠ 1 ∨ v31775 initial (inputs 0) = 1) = true
    simp [v31777, v31776, v14554, v14553, v11455, v24, reset]
  | succ t => exact task_46_from_event_and_pc _ _ _ pc event

#print axioms task_46_run_from_event_and_pc
end NutShellProofs
