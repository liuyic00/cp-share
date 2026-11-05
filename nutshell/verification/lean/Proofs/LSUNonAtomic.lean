import Proofs.LSUStateControl
namespace NutShellProofs
open nNutCore

/-- Without the atomic-operation bit, an idle outer LSU stays idle. -/
theorem non_atomic_lsu_stays_idle (s : State) (i : Inputs)
    (idle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (nonAtomic : BitVec.extractLsb' 5 1 (v28 s i) = 0) :
    (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0 := by
  have notLR : v11526 s i ≠ (32 : BitVec 7) := by
    intro h
    have bit := congrArg (BitVec.extractLsb' 5 1) h
    change BitVec.extractLsb' 5 1 (v28 s i) = _ at bit
    rw [nonAtomic] at bit
    contradiction
  have notSC : v11526 s i ≠ (33 : BitVec 7) := by
    intro h
    have bit := congrArg (BitVec.extractLsb' 5 1) h
    change BitVec.extractLsb' 5 1 (v28 s i) = _ at bit
    rw [nonAtomic] at bit
    contradiction
  have lr : v12332 s i = 0 := by exact if_neg notLR
  have sc : v11673 s i = 0 := by exact if_neg notSC
  have amo : v11583 s i = 0 := by
    simp [v11583, v11582, v11578, v11574, v11526, nonAtomic]
  change v12355 s i = 0
  simp [v12355, v12354, v12353, v11519, idle, v2687, v12336,
    v11674, sc, v12335, v12333, lr, v12334, amo]

/-- Entering a busy outer LSU state requires an active atomic request. -/
theorem lsu_busy_entry_requires_atomic_request (s : State) (i : Inputs)
    (idle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (busyNext : (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate ≠ 0) :
    v11525 s i = 1 ∧ BitVec.extractLsb' 5 1 (v28 s i) = 1 := by
  constructor
  · rcases BitVec.eq_zero_or_eq_one (v11525 s i) with zero | one
    · exact False.elim (busyNext (lsu_idle_without_request s i idle zero))
    · exact one
  · rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb' 5 1 (v28 s i)) with zero | one
    · exact False.elim (busyNext (non_atomic_lsu_stays_idle s i idle zero))
    · exact one


/-- This request-level condition is a remaining decode/whitelist obligation. -/
def NonAtomicLSURequest (s : State) (i : Inputs) : Prop :=
  v11525 s i = 1 → BitVec.extractLsb' 5 1 (v28 s i) = 0

theorem non_atomic_request_preserves_lsu_idle (s : State) (i : Inputs)
    (idle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (request : NonAtomicLSURequest s i) :
    (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0 := by
  rcases BitVec.eq_zero_or_eq_one (v11525 s i) with zero | one
  · exact lsu_idle_without_request s i idle zero
  · exact non_atomic_lsu_stays_idle s i idle (request one)

theorem non_atomic_requests_lsu_idle_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (requests : ∀ t, NonAtomicLSURequest (run initial inputs (t + 1)) (inputs (t + 1)))
    (t : Nat) :
    (run initial inputs (t + 1)).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0 := by
  induction t with
  | zero => exact lsu_idle_reset initial (inputs 0) reset
  | succ t ih => exact non_atomic_request_preserves_lsu_idle _ _ ih (requests t)

#print axioms non_atomic_requests_lsu_idle_run
#print axioms non_atomic_lsu_stays_idle
#print axioms lsu_busy_entry_requires_atomic_request
end NutShellProofs
