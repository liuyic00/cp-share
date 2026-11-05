import Proofs.LoadAddressRun
import Proofs.MemoryAlignmentCorrespondence
import Proofs.LSUExceptions
namespace NutShellProofs
open nNutCore

theorem enabled_misalignment_fault (s : State) (i : Inputs)
    (enabled : v11546 s i = 1) (misaligned : v11628 s i = 0) :
    v11632 s i = 1 ∨ v11638 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v11570 s i) with a | a <;>
    rcases BitVec.eq_zero_or_eq_one (v11584 s i) with b | b <;>
    simp [v11632, v11638, v11631, v11637, v11630, v11636,
      v11629, v11635, v11634, v11633, v11586, v11585, v11573,
      v11572, v11571, enabled, misaligned, a, b, v24]

theorem committed_normal_memory_enabled (s : State) (i next : Inputs)
    (operation : MemoryOp) (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (unit : v3 s i = 1) (commit : v9 (step s i) next = 1) : v11546 s i = 1 := by
  have valid := commit_requires_execute_valid s i next commit
  have flush := commit_requires_unflushed s i next commit
  cases operation <;>
    simp [v11546, v11545, v11519, v2687, outer, v11530, v11529, v11528,
      v11527, v11526, op, MemoryOp.control, v11525, v11524, v11523, v11522,
      v11521, v11520, unit, valid, flush, v24]

theorem committed_fault_disables_load_valid (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (fault : v11632 s i = 1 ∨ v11638 s i = 1) : v31121 (step s i) next = 0 := by
  have raised := lsu_fault_raises_exception s i fault
  have valid := commit_requires_execute_valid s i next commit
  have flush := commit_requires_unflushed s i next commit
  have reset := (next_commit_controls s i next commit).1
  have active : v13724 s i = 1 := by
    simp [v13724, v13723, v13722, valid, flush, v24]
  have trapped : v30821 (step s i) next = 1 := by
    change v14430 s i = 1
    rcases BitVec.eq_zero_or_eq_one (v13720 s i) with a | a <;>
      simp [v14430, v13172, v12103, v11455, reset, v14429, v14427, v14428,
        raised, active, a]
  simp [v31121, v31120, v31119, v31118, v31117, trapped, v110]
#print axioms enabled_misalignment_fault
#print axioms committed_normal_memory_enabled
#print axioms committed_fault_disables_load_valid
theorem load_address_task4_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (load : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    TaskHolds 4 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  rcases BitVec.eq_zero_or_eq_one (v11628 (run initial inputs (t + 1)) (inputs (t + 1))) with misaligned | aligned
  · have valid := commit_requires_execute_valid _ _ _ commit
    have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
    have enabled := committed_normal_memory_enabled _ _ _ operation op
      (original_assumptions_lsu_idle_run initial inputs reset environment t) unit commit
    have dut := committed_fault_disables_load_valid _ _ _ commit
      (enabled_misalignment_fault _ _ enabled misaligned)
    change v31121 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 at dut
    have refValid := load_alignment_matches_reference_valid_run initial inputs reset environment t
      operation load commit unit matched registers
    have refZero := refValid.symm.trans misaligned
    change decide (v31150 (run initial inputs (t + 2)) (inputs (t + 2)) ≠ 1 ∨
      v31147 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) = true
    simp [v31150, v31148, dut, refZero]
  · exact load_address_task4_aligned_run initial inputs reset environment t operation load
      commit unit matched registers aligned
#print axioms load_address_task4_run
end NutShellProofs
