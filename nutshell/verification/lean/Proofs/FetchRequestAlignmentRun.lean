import Proofs.FetchResponsePC
namespace NutShellProofs
open nNutCore

/-- Actual fetch enqueues cannot read idle, uninitialized response metadata. -/
theorem fetch_enqueue_requires_active_response (s : State) (i : Inputs)
    (enqueue : v10241 s i = 1) : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ 0 := by
  intro idle
  simp [v10241, v10240, v10239, v10238, v9709, v9708, v9707,
    v9706, v9705, v9704, v9702, v9701, idle] at enqueue

theorem fetch_enqueue_pc_aligned (s : State) (i : Inputs)
    (response : FetchResponsePCAligned s) (enqueue : v10241 s i = 1) :
    BitVec.extractLsb' 0 2 (v10265 s i) = 0 := by
  have low := response (fetch_enqueue_requires_active_response s i enqueue)
  simpa [v10265, v10264, v10263, v10262, v10261, v10260, v10259,
    v10258, v10257, low_low _ (by decide : 2 ≤ 39),
    low_low _ (by decide : 2 ≤ 82)] using low

theorem fetch_response_pc_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (requests : ∀ k, v25943 (run initial inputs (k + 1)) (inputs (k + 1)) = 1 →
      BitVec.extractLsb' 0 2 (run initial inputs (k + 1)).g33.r1065_nfrontend_5Fifu_5Fpc = 0)
    (t : Nat) : FetchResponsePCAligned (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact fetch_response_pc_reset _ _ reset
  | succ t ih => exact fetch_response_pc_step _ _ ih (requests t)

/-- Task zero follows from accepted request alignment. This remaining premise
is a hardware obligation, not an additional environment assumption. -/
theorem frontend_task0_run_of_requests (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (requests : ∀ k, v25943 (run initial inputs (k + 1)) (inputs (k + 1)) = 1 →
      BitVec.extractLsb' 0 2 (run initial inputs (k + 1)).g33.r1065_nfrontend_5Fifu_5Fpc = 0)
    (t : Nat) : TaskHolds 0 (run initial inputs t) (inputs t) := by
  apply frontend_task0_run_of_incoming initial inputs reset environment _ t
  intro k enqueue
  exact fetch_enqueue_pc_aligned _ _ (fetch_response_pc_run initial inputs reset requests k) enqueue
#print axioms fetch_enqueue_requires_active_response
#print axioms fetch_enqueue_pc_aligned
#print axioms fetch_response_pc_run
#print axioms frontend_task0_run_of_requests
end NutShellProofs
