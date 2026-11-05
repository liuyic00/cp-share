import Proofs.MemoryAlignmentHold
import Proofs.MemoryBusyFlush
import Proofs.MemoryBusyHold
namespace NutShellProofs
open nNutCore

structure MemoryBusyFacts (s : State) (i : Inputs) : Prop where
  valid : v6 s i = 1
  unit : v3 s i = 1
  aligned : v11628 s i = 1
  latched : MemoryAddressLatched s i
  flush : v24276 s i = 0

theorem memory_busy_facts_step (s : State) (i next : Inputs)
    (reset : i.g0.nreset = 0)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (nextOuter : (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (reachable : LSUInnerReachable s)
    (ordinary : v6 s i = 1 → v3 s i = 1 → ∃ op : MemoryOp, v28 s i = op.control)
    (old : s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0 → MemoryBusyFacts s i)
    (busy : (step s i).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0) :
    MemoryBusyFacts (step s i) next := by
  have controls : v6 s i = 1 ∧ v3 s i = 1 ∧ v11628 s i = 1 := by
    rcases lsu_inner_busy_predecessor s i busy with prior | request
    · exact ⟨(old prior).valid, (old prior).unit, (old prior).aligned⟩
    · obtain ⟨unit, valid, _⟩ := memory_request_execute_controls s i outer request
      exact ⟨valid, unit, memory_request_raw_alignment s i request⟩
  obtain ⟨operation, op⟩ := ordinary controls.1 controls.2.1
  obtain ⟨noFault, aligned⟩ := memory_raw_alignment_excludes_fault s i controls.2.2
  have hold := memory_next_busy_prevents_capture s i operation op outer reachable
    controls.2.1 controls.1 noFault aligned busy
  have nextAligned := (memory_raw_alignment_hold s i next outer nextOuter hold).trans controls.2.2
  have latched := memory_busy_address_latched_step s i next operation op reset outer nextOuter
    reachable controls.2.1 controls.1 noFault aligned busy (fun h => (old h).latched)
  have nextFlush := (normal_memory_next_busy_no_next_flush s i next operation op outer reachable
    controls.2.1 noFault aligned busy).2
  have nextUnit : v3 (step s i) next = 1 := by
    change v24913 s i = 1
    simpa only [v24913, hold, ↓reduceIte] using controls.2.1
  have identity : EXUPending (step s i) = some (EXUPair s) := by
    rcases lsu_inner_busy_predecessor s i busy with prior | request
    · have incomplete : v11698 s i = 0 := by
        rcases BitVec.eq_zero_or_eq_one (v11698 s i) with zero | one
        · exact zero
        · exact False.elim (busy (normal_memory_completion_returns_inner_idle s i operation
            op outer reachable noFault aligned one))
      have noComplete : v11702 s i ≠ 1 := by
        simp [v11702, v11701, v11700, v11495, v11494, controls.2.1, v11699,
          v11518, v11517, incomplete]
      rw [execute_pending_step s i reset (old prior).flush, if_neg hold, if_neg noComplete]
      exact if_pos controls.1
    · exact (memory_request_preserves_execute_identity s i next operation op reset outer request).1
  have nextValid : v6 (step s i) next = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v6 (step s i) next) with zero | one
    · change (step s i).g47.r1511_nbackend_5Fvalid = 0 at zero
      simp [EXUPending, zero] at identity
    · exact one
  exact ⟨nextValid, nextUnit, nextAligned, latched, nextFlush⟩
#print axioms memory_busy_facts_step
theorem memory_busy_facts_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (ordinary : ∀ k, v6 (run initial inputs (k + 1)) (inputs (k + 1)) = 1 →
      v3 (run initial inputs (k + 1)) (inputs (k + 1)) = 1 →
      ∃ op : MemoryOp, v28 (run initial inputs (k + 1)) (inputs (k + 1)) = op.control)
    (t : Nat)
    (busy : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0) :
    MemoryBusyFacts (run initial inputs (t + 1)) (inputs (t + 1)) := by
  induction t with
  | zero => exact False.elim (busy (lsu_inner_reset initial (inputs 0) reset))
  | succ t ih =>
    have currentReset : (inputs (t + 1)).g0.nreset = 0 := by
      rcases BitVec.eq_zero_or_eq_one (inputs (t + 1)).g0.nreset with zero | one
      · exact zero
      · exact False.elim (busy (lsu_inner_reset _ _ one))
    exact memory_busy_facts_step _ _ _ currentReset
      (original_assumptions_lsu_idle_run initial inputs reset environment t)
      (original_assumptions_lsu_idle_run initial inputs reset environment (t + 1))
      (lsu_inner_reachable_run initial inputs reset t) (ordinary t) ih busy
#print axioms memory_busy_facts_run
end NutShellProofs
