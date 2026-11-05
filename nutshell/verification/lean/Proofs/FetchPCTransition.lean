import Proofs.FetchResponseMetadata
namespace NutShellProofs
open nNutCore

/-- The exact fetch PC transition, with reset and redirect priority explicit. -/
theorem fetch_pc_transition (s : State) (i : Inputs) :
    (step s i).g33.r1065_nfrontend_5Fifu_5Fpc =
      if i.g0.nreset = 1 then 0x80000000
      else if v14 s i = 1 then v2709 s i
      else if v25943 s i = 1 then v2759 s i
      else s.g33.r1065_nfrontend_5Fifu_5Fpc := by
  change v9675 s i = _
  rcases BitVec.eq_zero_or_eq_one (v14 s i) with noRedirect | redirect <;>
    rcases BitVec.eq_zero_or_eq_one (v25943 s i) with noCapture | capture
  all_goals simp_all [v9675, v1, v0, v9671, v9674, v9673,
    ← fetch_capture_eq_advance, v2759]

theorem temporary_pc32_fetch_pc_transition (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    (run initial inputs (t + 2)).g33.r1065_nfrontend_5Fifu_5Fpc =
      if (inputs (t + 1)).g0.nreset = 1 then 0x80000000
      else if v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
        then v2709 (run initial inputs (t + 1)) (inputs (t + 1))
      else if v25943 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
        then (run initial inputs (t + 1)).g33.r1065_nfrontend_5Fifu_5Fpc + 4
      else (run initial inputs (t + 1)).g33.r1065_nfrontend_5Fifu_5Fpc := by
  rw [show run initial inputs (t + 2) = step (run initial inputs (t + 1)) (inputs (t + 1)) from rfl,
    fetch_pc_transition]
  rcases BitVec.eq_zero_or_eq_one (v14 (run initial inputs (t + 1)) (inputs (t + 1))) with noRedirect | redirect
  · by_cases capture : v25943 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
    · rw [temporary_pc32_accepted_fetch_target initial inputs reset environment restriction t capture noRedirect]
    · simp only [if_neg capture]
  · simp [redirect]

#print axioms fetch_pc_transition
#print axioms temporary_pc32_fetch_pc_transition

/-- Captured metadata carries exactly the IFU PC after the same transition. -/
theorem fetch_capture_successor_matches_next_pc (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (noRedirect : v14 s i = 0)
    (capture : v25943 s i = 1) :
    BitVec.extractLsb' 39 39 (step s i).g51.r1656_nio_5Fimem_5Fcache_5Fmemuser =
      (step s i).g33.r1065_nfrontend_5Fifu_5Fpc := by
  have metadata : (step s i).g51.r1656_nio_5Fimem_5Fcache_5Fmemuser = v25965 s i := by
    change v25966 s i = _
    rw [v25966, if_pos capture]
  rw [metadata, fetch_pc_transition]
  simp only [reset, noRedirect, capture, show (0 : BitVec 1) ≠ 1 by decide,
    ↓reduceIte]
  unfold v25965 v25964 v25963 v25962 v25961 v25960 v25959 v25958
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 39 + 39 ≤ 82),
    BitVec.extractLsb'_append_eq_of_le (by decide : 39 ≤ 39)]
  simp [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 39)]

#print axioms fetch_capture_successor_matches_next_pc
end NutShellProofs
