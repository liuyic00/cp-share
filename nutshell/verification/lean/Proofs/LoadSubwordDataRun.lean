import Proofs.LoadResponseOneCycle
import Proofs.MemoryBusyRun
namespace NutShellProofs
open nNutCore

theorem subword_checker_data_matches_lsu_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (extra : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 3) :
    (run initial inputs (t + 1)).g44.r1435_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Frdata =
      (run initial inputs (t + 1)).g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch := by
  have busy : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0 := by
    rw [extra]; decide
  cases t with
  | zero => exact False.elim (busy (lsu_inner_reset initial (inputs 0) reset))
  | succ t =>
    have prior := load_subword_cycle_predecessor _ _ extra
    have priorBusy : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0 := by
      rw [prior.1]; decide
    have facts := original_assumptions_memory_busy_run initial inputs reset environment t priorBusy
    have currentReset : (inputs (t + 1)).g0.nreset = 0 := by
      rcases BitVec.eq_zero_or_eq_one (inputs (t + 1)).g0.nreset with zero | one
      · exact zero
      · exact False.elim (busy (lsu_inner_reset _ _ one))
    exact response_captures_same_load_data _ _ currentReset facts.unit prior.2.2.1

theorem committed_subword_reference_data_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (extra : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 3) :
    v16181 (run initial inputs (t + 2)) (inputs (t + 2)) =
      (run initial inputs (t + 1)).g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch := by
  have noResponse := load_subword_cycle_has_no_new_response
    (run initial inputs t) (inputs t) (inputs (t + 1)) extra
  change v11661 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 at noResponse
  have captured := reference_load_data_capture _ _ _ commit unit
  rw [checker_load_data_latch_step _ _ (next_commit_controls _ _ _ commit).1 unit] at captured
  rw [noResponse] at captured
  simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte] at captured
  exact captured.trans (subword_checker_data_matches_lsu_run initial inputs reset environment t extra)
#print axioms subword_checker_data_matches_lsu_run
#print axioms committed_subword_reference_data_run
end NutShellProofs
