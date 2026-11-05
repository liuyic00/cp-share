import Proofs.FetchQueuePCOrder
namespace NutShellProofs
open nNutCore

/-- The PC accepted by IDU is the oldest pending fetch response. -/
theorem temporary_pc32_idu_capture_front (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (noRedirect : v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (capture : v11102 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    (FetchPCContents (run initial inputs (t + 1))).head? =
      some (v10174 (run initial inputs (t + 1)) (inputs (t + 1))) := by
  have dequeue := temporary_pc32_dequeue_eq_capture_run initial inputs reset
    environment restriction t currentReset noRedirect
  rw [temporary_pc32_frontend_output_pc_run initial inputs reset environment restriction t noRedirect]
  exact fetch_pc_dequeue_is_front _ _ (dequeue.trans capture)

/-- Actual fetch contents remove exactly the entry transferred to IDU. -/
theorem temporary_pc32_fetch_contents_transfer (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (noRedirect : v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    FetchPCContents (run initial inputs (t + 2)) =
      (if v11102 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
       then (FetchPCContents (run initial inputs (t + 1))).tail
       else FetchPCContents (run initial inputs (t + 1))) ++
      (if v10241 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
       then [v10265 (run initial inputs (t + 1)) (inputs (t + 1))] else []) := by
  have result := fetch_pc_contents_step (run initial inputs (t + 1))
    (inputs (t + 1)) currentReset noRedirect
  rw [temporary_pc32_dequeue_eq_capture_run initial inputs reset environment restriction t
    currentReset noRedirect] at result
  exact result

#print axioms temporary_pc32_idu_capture_front
#print axioms temporary_pc32_fetch_contents_transfer
end NutShellProofs
