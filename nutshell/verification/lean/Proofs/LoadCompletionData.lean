import Proofs.MemoryCompletion
import Proofs.ReferenceLoadDataCapture
import Proofs.LoadDataFormat
import Proofs.LoadWriteback
import Proofs.LoadSubwordDataRun
namespace NutShellProofs
open nNutCore

theorem ordinary_memory_completion (s : State) (i : Inputs)
    (operation : MemoryOp) (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (noFault : v11639 s i = 0) (aligned : v11640 s i = 0) :
    v11698 s i = v11665 s i := by
  have notSC : v11673 s i = 0 := by
    cases operation <;> simp [v11673, v11526, op, MemoryOp.control, v11672]
  simp [v11698, v11697, noFault, v11696, v11519, outer, v2687,
    v11676, v11675, v11674, notSC, v11667, v11666, aligned]

theorem ld_completion_requires_response (s : State) (i : Inputs)
    (op : v28 s i = MemoryOp.control .ld)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (noFault : v11639 s i = 0) (aligned : v11640 s i = 0)
    (complete : v11698 s i = 1) : v11661 s i = 1 := by
  rw [ordinary_memory_completion s i .ld op outer noFault aligned] at complete
  rcases BitVec.eq_zero_or_eq_one (v11661 s i) with zero | one
  · simp [v11665, v11644, v11643, v11642, v11569, v11568,
      v11519, outer, v2687, v11526, op, MemoryOp.control,
      v11664, v11662, zero] at complete
  · exact one

/-- On a non-faulting LD commit, actual DUT writeback equals reference raw data. -/
theorem committed_ld_writeback_reference_data (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 1)
    (op : v28 s i = MemoryOp.control .ld)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (noFault : v11639 s i = 0) (aligned : v11640 s i = 0) :
    v11842 (step s i) next = v16181 (step s i) next := by
  have response := ld_completion_requires_response s i op outer noFault aligned
    (lsu_commit_requires_completion s i next unit commit)
  rw [committed_response_reference_data s i next commit unit response]
  rw [writeback_ordinary_memory_result s i next .ld commit unit op outer]
  exact load_ld_formatted_result s i op outer
#print axioms ordinary_memory_completion
#print axioms ld_completion_requires_response
#print axioms committed_ld_writeback_reference_data
theorem narrow_load_completion_requires_extra_cycle (s : State) (i : Inputs)
    (operation : MemoryOp) (load : operation.isLoad = true) (narrow : operation ≠ .ld)
    (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (noFault : v11639 s i = 0) (aligned : v11640 s i = 0)
    (complete : v11698 s i = 1) :
    s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 3 := by
  rw [ordinary_memory_completion s i operation op outer noFault aligned] at complete
  have selector : v11644 s i = 1 := by
    cases operation <;> simp_all [MemoryOp.isLoad, v11644, v11641, v11571,
      v11570, v24, v11643, v11642, v11569, v11568, v11519, v2687,
      v11526, MemoryOp.control]
  simpa [v11665, selector, v11645, v2750] using complete
#print axioms narrow_load_completion_requires_extra_cycle
theorem nonfaulting_narrow_load_reference_data_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (operation : MemoryOp) (load : operation.isLoad = true) (narrow : operation ≠ .ld)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (noFault : v11639 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (aligned : v11640 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v16181 (run initial inputs (t + 2)) (inputs (t + 2)) =
      (run initial inputs (t + 1)).g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  have extra := narrow_load_completion_requires_extra_cycle _ _ operation load narrow op
    (original_assumptions_lsu_idle_run initial inputs reset environment t) noFault aligned
    (lsu_commit_requires_completion _ _ _ unit commit)
  exact committed_subword_reference_data_run initial inputs reset environment t commit unit extra
#print axioms nonfaulting_narrow_load_reference_data_run
end NutShellProofs
