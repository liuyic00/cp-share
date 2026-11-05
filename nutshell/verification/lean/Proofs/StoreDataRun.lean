import Proofs.StoreDataHold
import Proofs.MemoryMaskRun
namespace NutShellProofs
open nNutCore
theorem original_assumptions_busy_store_data_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (busy : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0) :
    StoreDataLatched (run initial inputs (t + 1)) (inputs (t + 1)) := by
  induction t with
  | zero => exact False.elim (busy (lsu_inner_reset initial (inputs 0) reset))
  | succ t ih =>
    have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
    have nextOuter := original_assumptions_lsu_idle_run initial inputs reset environment (t + 1)
    have controls : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 ∧
        v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 ∧
        v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 ∧
        v11546 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 := by
      rcases lsu_inner_busy_predecessor _ _ busy with prior | request
      · have facts := original_assumptions_memory_busy_run initial inputs reset environment t prior
        exact ⟨facts.valid, facts.unit, facts.aligned,
          original_assumptions_busy_enabled_run initial inputs reset environment t prior⟩
      · obtain ⟨unit, valid, flush⟩ := memory_request_execute_controls _ _ outer request
        obtain ⟨operation, _, op⟩ := original_assumptions_lsu_memory_run initial inputs reset environment t valid unit
        exact ⟨valid, unit, memory_request_raw_alignment _ _ request,
          normal_memory_enabled _ _ operation op outer unit valid flush⟩
    obtain ⟨operation, _, op⟩ := original_assumptions_lsu_memory_run initial inputs reset environment t controls.1 controls.2.1
    obtain ⟨noFault, aligned⟩ := memory_raw_alignment_excludes_fault _ _ controls.2.2.1
    have hold := memory_next_busy_prevents_capture _ _ operation op outer
      (lsu_inner_reachable_run initial inputs reset t) controls.2.1 controls.1 noFault aligned busy
    have currentReset : (inputs (t + 1)).g0.nreset = 0 := by
      rcases BitVec.eq_zero_or_eq_one (inputs (t + 1)).g0.nreset with zero | one
      · exact zero
      · exact False.elim (busy (lsu_inner_reset _ _ one))
    apply store_data_latched_step _ _ _ currentReset controls.2.1 outer nextOuter hold
    rcases lsu_inner_busy_predecessor _ _ busy with prior | request
    · exact Or.inr (ih prior)
    · exact Or.inl request
#print axioms original_assumptions_busy_store_data_run
end NutShellProofs
