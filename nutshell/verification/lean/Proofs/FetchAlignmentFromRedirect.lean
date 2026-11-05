import Proofs.PredictionFetchExclusion
import Proofs.FetchRequestAlignmentRun
namespace NutShellProofs
open nNutCore

/-- For this generated blocking-fetch design, only reachable redirects remain
as target-alignment obligations; unused BTB/RAS predictions need not be aligned. -/
theorem fetch_pc_aligned_run_of_redirects (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (redirects : ∀ t, v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 →
      BitVec.extractLsb' 0 2 (v2709 (run initial inputs (t + 1)) (inputs (t + 1))) = 0)
    (t : Nat) : BitVec.extractLsb' 0 2
      (run initial inputs (t + 1)).g33.r1065_nfrontend_5Fifu_5Fpc = 0 := by
  induction t with
  | zero =>
    change BitVec.extractLsb' 0 2 (v9675 initial (inputs 0)) = 0
    rw [v9675]
    have r : v1 initial (inputs 0) = 1 := reset
    rw [if_pos r]
    unfold v9671
    decide
  | succ t ih =>
    apply fetch_pc_alignment_step _ _ ih
    intro update
    have clear := crossline_latch_clear_run initial inputs reset t
    by_cases redirect : v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
    · simpa only [v2759, if_pos redirect] using redirects t redirect
    · have noPrediction : v2736 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 1 := by
        intro prediction
        exact redirect (prediction_update_requires_redirect (run initial inputs t)
          (inputs t) (inputs (t + 1)) (Or.inl prediction) update)
      have sequential := fetch_sequential_target_aligned
        (run initial inputs (t + 1)) (inputs (t + 1)) ih
      simpa only [v2759, if_neg redirect, v2758, clear, show (0 : BitVec 1) ≠ 1 by decide,
        ↓reduceIte, v2757, if_neg noPrediction] using sequential

theorem frontend_task0_run_of_redirects (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (redirects : ∀ t, v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 →
      BitVec.extractLsb' 0 2 (v2709 (run initial inputs (t + 1)) (inputs (t + 1))) = 0)
    (t : Nat) : TaskHolds 0 (run initial inputs t) (inputs t) := by
  apply frontend_task0_run_of_requests initial inputs reset environment _ t
  intro k _
  exact fetch_pc_aligned_run_of_redirects initial inputs reset redirects k

#print axioms fetch_pc_aligned_run_of_redirects
#print axioms frontend_task0_run_of_redirects
end NutShellProofs
