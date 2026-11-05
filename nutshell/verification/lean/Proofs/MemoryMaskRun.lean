import Proofs.MemoryMaskHold
namespace NutShellProofs
open nNutCore

theorem normal_memory_enabled (s : State) (i : Inputs)
    (operation : MemoryOp) (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (unit : v3 s i = 1) (valid : v6 s i = 1) (flush : v23 s i = 0) :
    v11546 s i = 1 := by
  cases operation <;>
    simp [v11546, v11545, v11519, v2687, outer, v11530, v11529, v11528,
      v11527, v11526, op, MemoryOp.control, v11525, v11524, v11523, v11522,
      v11521, v11520, unit, valid, flush, v24]

theorem execute_flush_zero_wbu_flush_zero (s : State) (i : Inputs)
    (clear : v24276 s i = 0) : v23 s i = 0 := by
  rcases BitVec.eq_zero_or_eq_one (v14 s i) with zero | one
  · simp [v23, v22, v21, v20, v19, v18, v17, zero, v16]
  · simp [v24276, v21, v20, v19, v18, v17, one, v15] at clear

theorem original_assumptions_busy_enabled_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (busy : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0) :
    v11546 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 := by
  have facts := original_assumptions_memory_busy_run initial inputs reset environment t busy
  obtain ⟨operation, _, op⟩ := original_assumptions_lsu_memory_run initial inputs reset environment t facts.valid facts.unit
  exact normal_memory_enabled _ _ operation op
    (original_assumptions_lsu_idle_run initial inputs reset environment t) facts.unit facts.valid
    (execute_flush_zero_wbu_flush_zero _ _ facts.flush)

theorem original_assumptions_busy_masks_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (busy : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0) :
    MemoryMasksLatched (run initial inputs (t + 1)) (inputs (t + 1)) := by
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
    have enabled : v11546 (step (run initial inputs (t + 1)) (inputs (t + 1))) (inputs (t + 2)) =
        v11546 (run initial inputs (t + 1)) (inputs (t + 1)) :=
      (original_assumptions_busy_enabled_run initial inputs reset environment (t + 1) busy).trans controls.2.2.2.symm
    have stable := memory_mask_routing_hold _ _ _ outer nextOuter hold enabled
    have currentReset : (inputs (t + 1)).g0.nreset = 0 := by
      rcases BitVec.eq_zero_or_eq_one (inputs (t + 1)).g0.nreset with zero | one
      · exact zero
      · exact False.elim (busy (lsu_inner_reset _ _ one))
    apply memory_masks_latched_step _ _ _ currentReset controls.2.1 stable.1 stable.2
    rcases lsu_inner_busy_predecessor _ _ busy with prior | request
    · exact Or.inr (ih prior)
    · exact Or.inl request
#print axioms original_assumptions_busy_enabled_run
#print axioms original_assumptions_busy_masks_run
end NutShellProofs
