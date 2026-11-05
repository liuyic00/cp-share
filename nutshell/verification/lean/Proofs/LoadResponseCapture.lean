import Proofs.MemoryCompletion
import Proofs.LoadByteSelection
namespace NutShellProofs
open nNutCore

theorem load_data_latch_step (s : State) (i : Inputs) :
    (step s i).g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch = v12306 s i := by
  rfl

theorem load_address_latch_step (s : State) (i : Inputs) :
    (step s i).g41.r1333_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FaddrLatch = v11612 s i := by
  rfl

/-- The extra narrow-load cycle can only follow an accepted response while waiting. -/
theorem load_subword_cycle_predecessor (s : State) (i : Inputs)
    (extra : (step s i).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 3) :
    s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 2 ∧
      v11646 s i = 1 ∧ v11661 s i = 1 ∧ v11644 s i = 1 := by
  change v12276 s i = 3 at extra
  have cases : ∀ x : BitVec 2, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases cases s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate with h | h | h | h <;>
    rcases BitVec.eq_zero_or_eq_one (v11646 s i) with ready | ready <;>
    rcases BitVec.eq_zero_or_eq_one (v11661 s i) with response | response <;>
    rcases BitVec.eq_zero_or_eq_one (v11644 s i) with narrow | narrow <;>
    rcases BitVec.eq_zero_or_eq_one (v12235 s i) with reset | reset <;>
    rcases BitVec.eq_zero_or_eq_one (v12264 s i) with request | request <;>
    simp_all [v12276, v12275, v12236, v12265, v12274, v12266, v12273,
      v12267, v12270, v12268, v12269, v12272, v12271, v2750, v9721, v4079, v10089]


/-- Data and address in the extra cycle come from the same prior cycle that accepted the response. -/
theorem load_subword_response_capture (s : State) (i : Inputs)
    (extra : (step s i).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 3) :
    v11646 s i = 1 ∧ v11661 s i = 1 ∧
    (step s i).g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch = v12306 s i ∧
    (step s i).g41.r1333_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FaddrLatch = v11612 s i := by
  have prior := load_subword_cycle_predecessor s i extra
  exact ⟨prior.2.1, prior.2.2.1, rfl, rfl⟩
#print axioms load_subword_cycle_predecessor
#print axioms load_subword_response_capture
end NutShellProofs
