import Proofs.FetchQueuePCAlignment
namespace NutShellProofs
open nNutCore

/-- Only active transactions constrain the unreset response metadata latch. -/
def FetchResponsePCAligned (s : State) : Prop :=
  s.g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ 0 →
    BitVec.extractLsb' 0 2 s.g51.r1656_nio_5Fimem_5Fcache_5Fmemuser = 0

theorem fetch_response_pc_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    FetchResponsePCAligned (step s i) := by
  intro active
  change v25883 s i ≠ 0 at active
  simp [v25883, v25803, reset, v2687] at active

theorem fetch_request_metadata_pc (s : State) (i : Inputs) :
    BitVec.extractLsb' 0 2 (v25965 s i) =
      BitVec.extractLsb' 0 2 s.g33.r1065_nfrontend_5Fifu_5Fpc := by
  simp [v25965, v25964, v25963, v25962, v25961, v25960, v25959,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 82),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 39)]

theorem fetch_response_pc_step (s : State) (i : Inputs)
    (old : FetchResponsePCAligned s)
    (request : v25943 s i = 1 → BitVec.extractLsb' 0 2 s.g33.r1065_nfrontend_5Fifu_5Fpc = 0) :
    FetchResponsePCAligned (step s i) := by
  intro active
  change BitVec.extractLsb' 0 2 (v25966 s i) = 0
  by_cases capture : v25943 s i = 1
  · rw [v25966, if_pos capture, fetch_request_metadata_pc]
    exact request capture
  · rw [v25966, if_neg capture]
    apply old
    intro idle
    have noRequest : v25808 s i ≠ 1 := by
      intro requested
      apply capture
      simp [v25943, v2689, v2688, idle, v2687, requested]
    have noStart : v25818 s i = 0 := by
      rcases BitVec.eq_zero_or_eq_one (v25808 s i) with zero | one
      · simp [v25818, v25809, zero]
      · exact False.elim (noRequest one)
    change v25883 s i ≠ 0 at active
    simp [v25883, v25882, v25804, idle, v2687, v25839, noStart] at active
#print axioms fetch_response_pc_reset
#print axioms fetch_request_metadata_pc
#print axioms fetch_response_pc_step
end NutShellProofs
