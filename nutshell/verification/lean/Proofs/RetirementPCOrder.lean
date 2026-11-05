import Proofs.PCSequence
namespace NutShellProofs
open nNutCore

noncomputable def RetirementPCs (s : State) : List (BitVec 39) :=
  (if s.g48.r1567_nbackend_5Fvalid_5F1 = 1 then [(WBUPair s).2] else []) ++ IssuedPCs s

theorem writeback_valid_eq_completion (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v14 s i = 0) :
    (step s i).g48.r1567_nbackend_5Fvalid_5F1 = v11702 s i := by
  have redirect := (pipeline_flush_signals s i).2.2.trans flush
  change v25331 s i = _
  rcases BitVec.eq_zero_or_eq_one (v11702 s i) with zero | one
  all_goals simp_all [v25331, v11455, v25330, v25329, v11492, v110]

theorem execute_completion_is_issued_front (s : State) (i : Inputs)
    (complete : v11702 s i = 1) : (IssuedPCs s).head? = some (EXUPair s).2 := by
  simp [IssuedPCs, InstructionPCs, PipelinePending, EXUPending,
    execute_completion_requires_valid s i complete]

theorem retirement_pcs_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v14 s i = 0)
    (bound : QueueOccupancy s ≤ 2)
    (handshake : v11083 s i = v11102 s i)
    (front : v11102 s i = 1 → (FetchPCContents s).head? = some (v10174 s i))
    (notDelivered : FetchNotAlreadyDelivered s) :
    RetirementPCs (step s i) = IssuedPCs s ++
      (if v25943 s i = 1 then [s.g33.r1065_nfrontend_5Fifu_5Fpc] else []) := by
  unfold RetirementPCs
  rw [writeback_valid_eq_completion s i reset flush,
    issued_pcs_step s i reset flush bound handshake front notDelivered]
  by_cases complete : v11702 s i = 1
  · have commit : v9 (step s i) i = 1 := (writeback_valid_eq_completion s i reset flush).trans complete
    rw [committed_pair_is_execute_pair s i i commit]
    simp only [if_pos complete, ← List.append_assoc]
    have first := execute_completion_is_issued_front s i complete
    have restored : [(EXUPair s).2] ++ (IssuedPCs s).tail = IssuedPCs s := by
      cases h : IssuedPCs s with
      | nil => simp [h] at first
      | cons pc rest =>
        simp only [h, List.head?_cons, Option.some.injEq] at first
        simp [first]
    rw [restored]
  · simp only [if_neg complete, List.nil_append]

/-- Removing the currently committing WBU entry exposes the issued sequence. -/
theorem retirement_pcs_after_commit (s : State) (i : Inputs) :
    (if v9 s i = 1 then (RetirementPCs s).tail else RetirementPCs s) = IssuedPCs s := by
  rcases BitVec.eq_zero_or_eq_one s.g48.r1567_nbackend_5Fvalid_5F1 with zero | one
  all_goals simp_all [RetirementPCs, v9]

#print axioms retirement_pcs_step

theorem retirement_pcs_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    RetirementPCs (step s i) = [] := by
  have clear : (step s i).g48.r1567_nbackend_5Fvalid_5F1 = 0 := by
    change v25331 s i = 0
    simp [v25331, v11455, reset, v24]
  simp [RetirementPCs, clear, issued_pcs_reset s i reset]

theorem retirement_pcs_flush (s : State) (i : Inputs) (flush : v14 s i = 1) :
    RetirementPCs (step s i) = [] := by
  have redirect := (pipeline_flush_signals s i).2.2.trans flush
  have clear : (step s i).g48.r1567_nbackend_5Fvalid_5F1 = 0 := by
    change v25331 s i = 0
    simp [v25331, v25330, redirect, v24]
  simp [RetirementPCs, clear, issued_pcs_flush s i flush]

theorem temporary_pc32_retirement_pcs_sequential (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    SequentialPCs (RetirementPCs (run initial inputs (t + 1)))
      (run initial inputs (t + 1)).g33.r1065_nfrontend_5Fifu_5Fpc := by
  cases t with
  | zero =>
    rw [show run initial inputs (0 + 1) = step initial (inputs 0) from rfl,
      retirement_pcs_reset initial (inputs 0) reset]
    exact sequential_pcs_empty _
  | succ t =>
    rcases BitVec.eq_zero_or_eq_one (inputs (t + 1)).g0.nreset with noReset | currentReset
    · rcases BitVec.eq_zero_or_eq_one (v14 (run initial inputs (t + 1)) (inputs (t + 1))) with noRedirect | redirect
      · have transition := retirement_pcs_step (run initial inputs (t + 1)) (inputs (t + 1))
          noReset noRedirect (queue_occupancy_bound_run initial inputs reset t)
          (temporary_pc32_dequeue_eq_capture_run initial inputs reset environment restriction t noReset noRedirect)
          (temporary_pc32_idu_capture_front initial inputs reset environment restriction t noReset noRedirect)
          (fetch_not_delivered_run initial inputs reset t)
        have pc := temporary_pc32_fetch_pc_transition initial inputs reset environment restriction t
        change SequentialPCs (RetirementPCs (run initial inputs (t + 2))) _
        change RetirementPCs (run initial inputs (t + 2)) = _ at transition
        rw [transition, pc]
        have old := temporary_pc32_issued_pcs_sequential initial inputs reset environment restriction t
        rcases BitVec.eq_zero_or_eq_one (v25943 (run initial inputs (t + 1)) (inputs (t + 1))) with noCapture | capture
        · simpa [noReset, noRedirect, noCapture] using old
        · simpa [noReset, noRedirect, capture] using sequential_pcs_append_next _ _ old
      · change SequentialPCs (RetirementPCs (step (run initial inputs (t + 1)) (inputs (t + 1)))) _
        rw [retirement_pcs_flush _ _ redirect]
        exact sequential_pcs_empty _
    · change SequentialPCs (RetirementPCs (step (run initial inputs (t + 1)) (inputs (t + 1)))) _
      rw [retirement_pcs_reset _ _ currentReset]
      exact sequential_pcs_empty _

#print axioms temporary_pc32_retirement_pcs_sequential
end NutShellProofs
