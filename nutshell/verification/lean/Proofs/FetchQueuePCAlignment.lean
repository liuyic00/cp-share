import Proofs.FrontendAssertionRun
namespace NutShellProofs
open nNutCore
def FetchQueuePCAligned (s : State) : Prop :=
  BitVec.extractLsb' 0 2 s.g33.r1083_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F0_5Fpc = 0 ∧
  BitVec.extractLsb' 0 2 s.g35.r1122_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F1_5Fpc = 0 ∧
  BitVec.extractLsb' 0 2 s.g36.r1161_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F2_5Fpc = 0 ∧
  BitVec.extractLsb' 0 2 s.g37.r1200_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F3_5Fpc = 0

theorem fetch_queue_pc_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    FetchQueuePCAligned (step s i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change BitVec.extractLsb' 0 2 (v10268 s i) = 0
    simp [v10268, v10235, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v10542 s i) = 0
    simp [v10542, v10235, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v10735 s i) = 0
    simp [v10735, v10235, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v10891 s i) = 0
    simp [v10891, v10235, v0, reset, v8200]

theorem fetch_queue_pc_step (s : State) (i : Inputs)
    (old : FetchQueuePCAligned s)
    (incoming : v10241 s i = 1 → BitVec.extractLsb' 0 2 (v10265 s i) = 0) :
    FetchQueuePCAligned (step s i) := by
  rcases old with ⟨h0,h1,h2,h3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change BitVec.extractLsb' 0 2 (v10268 s i) = 0
    unfold v10268 v10267 v10266
    repeat' split
    all_goals first | exact h0 | exact incoming (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v10542 s i) = 0
    unfold v10542 v10541 v10540
    repeat' split
    all_goals first | exact h1 | exact incoming (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v10735 s i) = 0
    unfold v10735 v10734 v10733
    repeat' split
    all_goals first | exact h2 | exact incoming (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v10891 s i) = 0
    unfold v10891 v10890 v10889
    repeat' split
    all_goals first | exact h3 | exact incoming (by assumption) | rfl

theorem fetch_queue_pc_selected (s : State) (i : Inputs) (old : FetchQueuePCAligned s) :
    BitVec.extractLsb' 0 2 (v9733 s i) = 0 := by
  rcases old with ⟨h0,h1,h2,h3⟩
  have bound := s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.isLt
  have cases : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 0 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 1 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 2 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v9733, v9732, v9731, v9730, v9729, v9728, v9727, v9726, v9725, v9724, v9723, v9722, v9721, v9720, v2750, v110, ptr] using h0
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v9733, v9732, v9731, v9730, v9729, v9728, v9727, v9726, v9725, v9724, v9723, v9722, v9721, v9720, v2750, v110, ptr] using h1
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v9733, v9732, v9731, v9730, v9729, v9728, v9727, v9726, v9725, v9724, v9723, v9722, v9721, v9720, v2750, v110, ptr] using h2
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v9733, v9732, v9731, v9730, v9729, v9728, v9727, v9726, v9725, v9724, v9723, v9722, v9721, v9720, v2750, v110, ptr] using h3
/-- Queue alignment follows from alignment of actual enqueues only. -/
theorem fetch_queue_pc_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (incoming : ∀ k, v10241 (run initial inputs (k + 1)) (inputs (k + 1)) = 1 →
      BitVec.extractLsb' 0 2 (v10265 (run initial inputs (k + 1)) (inputs (k + 1))) = 0)
    (t : Nat) : FetchQueuePCAligned (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact fetch_queue_pc_reset _ _ reset
  | succ t ih => exact fetch_queue_pc_step _ _ ih (incoming t)

/-- Original task zero reduced to the PC carried by actual fetch enqueues. -/
theorem frontend_task0_run_of_incoming (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (incoming : ∀ k, v10241 (run initial inputs (k + 1)) (inputs (k + 1)) = 1 →
      BitVec.extractLsb' 0 2 (v10265 (run initial inputs (k + 1)) (inputs (k + 1))) = 0)
    (t : Nat) : TaskHolds 0 (run initial inputs t) (inputs t) := by
  apply frontend_task0_run_of_head initial inputs reset environment _ t
  intro k _
  exact fetch_queue_pc_selected _ _ (fetch_queue_pc_run initial inputs reset incoming k)
#print axioms fetch_queue_pc_run
#print axioms frontend_task0_run_of_incoming
#print axioms fetch_queue_pc_reset
#print axioms fetch_queue_pc_step
#print axioms fetch_queue_pc_selected
end NutShellProofs
