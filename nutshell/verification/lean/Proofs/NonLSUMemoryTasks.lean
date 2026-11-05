import Proofs.NonMemoryDispatchRun
import Proofs.ReferenceNonMemoryEvents
namespace NutShellProofs
open nNutCore

theorem memory_match_low32_lift (operation : MemoryOp) (instr : BitVec 64)
    (matched : BitVec.extractLsb' 0 32 instr &&& 28799 = operation.encoding.setWidth 32) :
    IsMemory operation instr := by
  have lifted := instruction_mask_low32_lift instr 28799 (operation.encoding.setWidth 32) matched
  cases operation <;> simpa [IsMemory, MemoryOp.encoding] using lifted

theorem committed_non_lsu_non_csr_reference_events_run
    (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (notLSU : v3 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 1)
    (notCSR : v3 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 3) :
    v31135 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 ∧
    v31224 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
  apply reference_nonmemory_events_zero
  intro operation matched
  have instruction := committed_reference_instruction _ _ _ commit
  change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
    BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
  rw [instruction] at matched
  exact non_lsu_non_csr_instruction_run initial inputs reset t
    (commit_requires_execute_valid _ _ _ commit) notLSU notCSR operation
    (memory_match_low32_lift operation _ matched)
#print axioms committed_non_lsu_non_csr_reference_events_run

theorem committed_non_lsu_non_csr_memory_tasks_run
    (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (notLSU : v3 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 1)
    (notCSR : v3 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 3) :
    ∀ task : Fin 48, 3 ≤ task.val → task.val ≤ 9 →
      TaskHolds task (run initial inputs (t + 2)) (inputs (t + 2)) := by
  obtain ⟨dutLoad, dutStore⟩ := committed_non_lsu_events_zero _ _ _ commit notLSU
  obtain ⟨refLoad, refStore⟩ := committed_non_lsu_non_csr_reference_events_run
    initial inputs reset t commit notLSU notCSR
  obtain ⟨h3,h4,h5⟩ := absent_load_tasks _ _ dutLoad refLoad
  obtain ⟨h6,h7,h8,h9⟩ := absent_store_tasks _ _ dutStore refStore
  intro task lo hi
  have cases : task = 3 ∨ task = 4 ∨ task = 5 ∨ task = 6 ∨ task = 7 ∨ task = 8 ∨ task = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
#print axioms committed_non_lsu_non_csr_memory_tasks_run
/-- Covers idle cycles and every committed execution unit except CSR.
The CSR condition is local to this lemma, not an added model assumption. -/
theorem non_csr_memory_tasks_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (notCSR : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 →
      v3 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 3)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    ∀ task : Fin 48, 3 ≤ task.val → task.val ≤ 9 →
      TaskHolds task (run initial inputs (t + 2)) (inputs (t + 2)) := by
  rcases BitVec.eq_zero_or_eq_one (v9 (run initial inputs (t + 2)) (inputs (t + 2))) with idle | commit
  · exact no_commit_memory_tasks _ _ idle
  · by_cases unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
    · exact committed_lsu_memory_tasks_run initial inputs reset environment t commit unit registers
    · exact committed_non_lsu_non_csr_memory_tasks_run initial inputs reset t commit unit (notCSR commit)
#print axioms non_csr_memory_tasks_run
end NutShellProofs
