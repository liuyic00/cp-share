import Proofs.LoadDataFormat
import Proofs.MemoryBusyRun
import Proofs.WritebackSelection
namespace NutShellProofs
open nNutCore

/-- Ordinary memory operations bypass the atomic-result and store-conditional muxes. -/
theorem ordinary_memory_result (s : State) (i : Inputs) (operation : MemoryOp)
    (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    v25537 s i = v12460 s i := by
  have notSC : v11673 s i = 0 := by
    cases operation <;> simp [v11673, v11526, op, MemoryOp.control, v11672]
  simp [v25537, v25100, v25099, v11674, notSC, v25098, v25097, outer, v11535, v12461]

theorem writeback_ordinary_memory_result (s : State) (i next : Inputs) (operation : MemoryOp)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 1)
    (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    v11842 (step s i) next = v12460 s i := by
  exact (writeback_capture_1 s i next commit unit).trans
    (ordinary_memory_result s i operation op outer)

theorem original_assumptions_memory_writeback_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v12460 (run initial inputs (t + 1)) (inputs (t + 1)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨operation, _, op⟩ := original_assumptions_lsu_memory_run initial inputs reset environment t valid unit
  exact writeback_ordinary_memory_result _ _ _ operation commit unit op
    (original_assumptions_lsu_idle_run initial inputs reset environment t)
#print axioms ordinary_memory_result
#print axioms writeback_ordinary_memory_result
#print axioms original_assumptions_memory_writeback_run
end NutShellProofs
