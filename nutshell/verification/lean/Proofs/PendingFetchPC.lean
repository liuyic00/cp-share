import Proofs.FetchLiveRequest
namespace NutShellProofs
open nNutCore

noncomputable def PendingFetchPC (s : State) : List (BitVec 39) :=
  @ite _ (LiveFetchRequest s) (Classical.propDecidable _) [BitVec.extractLsb' 0 39 s.g51.r1656_nio_5Fimem_5Fcache_5Fmemuser] []

theorem pending_fetch_pc_capture (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (redirect : v14 s i = 0)
    (capture : v25943 s i = 1) :
    PendingFetchPC (step s i) = [s.g33.r1065_nfrontend_5Fifu_5Fpc] := by
  rw [PendingFetchPC, if_pos (fetch_capture_becomes_live s i reset redirect capture)]
  change [BitVec.extractLsb' 0 39 (v25966 s i)] = _
  rw [v25966, if_pos capture]
  simp [v25965, v25964, v25963, v25962, v25961, v25960, v25959, v25958,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 82),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 39)]

theorem pending_fetch_pc_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (redirect : v14 s i = 0)
    (notDelivered : FetchNotAlreadyDelivered s) :
    PendingFetchPC (step s i) =
      if v25943 s i = 1 then [s.g33.r1065_nfrontend_5Fifu_5Fpc]
      else if v10241 s i = 1 then [] else PendingFetchPC s := by
  by_cases capture : v25943 s i = 1
  · rw [if_pos capture]
    exact pending_fetch_pc_capture s i reset redirect capture
  · rw [if_neg capture]
    have metadata : (step s i).g51.r1656_nio_5Fimem_5Fcache_5Fmemuser =
        s.g51.r1656_nio_5Fimem_5Fcache_5Fmemuser := by
      change v25966 s i = _
      rw [v25966, if_neg capture]
    have live := live_fetch_request_step s i reset redirect notDelivered
    rcases BitVec.eq_zero_or_eq_one (v10241 s i) with zero | one
    · simp only [capture, false_or, zero] at live
      simp at live
      by_cases old : LiveFetchRequest s
      · have next := live.mpr old
        simp [PendingFetchPC, old, next, metadata, zero]
      · have next : ¬ LiveFetchRequest (step s i) := fun h => old (live.mp h)
        simp [PendingFetchPC, old, next, zero]
    · have dead : ¬ LiveFetchRequest (step s i) := by
        intro next
        rcases live.mp next with accepted | held
        · exact capture accepted
        · rw [one] at held
          simp at held
      simp [one, PendingFetchPC, dead]

theorem pending_fetch_pc_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    PendingFetchPC (step s i) = [] := by
  rw [PendingFetchPC, if_neg (fetch_reset_not_live s i reset)]

theorem pending_fetch_pc_flush (s : State) (i : Inputs) (redirect : v14 s i = 1) :
    PendingFetchPC (step s i) = [] := by
  rw [PendingFetchPC, if_neg (fetch_redirect_not_live s i redirect)]

#print axioms pending_fetch_pc_step

theorem pending_fetch_pc_enqueued (s : State) (i : Inputs)
    (enqueue : v10241 s i = 1) : PendingFetchPC s = [v10265 s i] := by
  have clear : s.g51.r1645_nio_5Fimem_5Fcache_5FneedFlush = 0 := by
    rcases BitVec.eq_zero_or_eq_one s.g51.r1645_nio_5Fimem_5Fcache_5FneedFlush with zero | one
    · exact zero
    · simp [v10241, v10240, v10239, v10238, v10237, v10236,
        v9709, v9708, v9707, v9706, v9705, v9704, v9703, v24, one] at enqueue
  have live : LiveFetchRequest s := ⟨fetch_enqueue_requires_active_response s i enqueue, clear⟩
  rw [PendingFetchPC, if_pos live]
  simp [v10265, v10264, v10263, v10262, v10261, v10260, v10259, v10258, v10257,
    low_low _ (by decide : 39 ≤ 82)]

theorem pending_fetch_pc_before_capture (s : State) (i : Inputs)
    (capture : v25943 s i = 1) : PendingFetchPC s = [] := by
  have idle := fetch_capture_requires_idle s i capture
  have dead : ¬ LiveFetchRequest s := fun h => h.1 idle
  rw [PendingFetchPC, if_neg dead]

theorem pending_fetch_pc_transfer (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (redirect : v14 s i = 0)
    (notDelivered : FetchNotAlreadyDelivered s) :
    (if v10241 s i = 1 then [v10265 s i] else []) ++ PendingFetchPC (step s i) =
      PendingFetchPC s ++ (if v25943 s i = 1 then [s.g33.r1065_nfrontend_5Fifu_5Fpc] else []) := by
  rw [pending_fetch_pc_step s i reset redirect notDelivered]
  by_cases enqueue : v10241 s i = 1
  · have noCapture := fetch_enqueue_excludes_capture s i enqueue
    rw [pending_fetch_pc_enqueued s i enqueue]
    simp [enqueue, noCapture]
  · by_cases capture : v25943 s i = 1
    · rw [pending_fetch_pc_before_capture s i capture]
      simp only [if_neg enqueue, if_pos capture, List.nil_append]
    · simp only [if_neg enqueue, if_neg capture, List.nil_append, List.append_nil]

#print axioms pending_fetch_pc_transfer
end NutShellProofs
