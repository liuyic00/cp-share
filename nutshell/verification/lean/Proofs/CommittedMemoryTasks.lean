import Proofs.ReferenceMemoryDirection
import Proofs.MemoryValidTasks
import Proofs.StoreDataTask
namespace NutShellProofs
open nNutCore
theorem absent_load_tasks (s : State) (i : Inputs)
    (dut : v31121 s i = 0) (reference : v31135 s i = 0) :
    TaskHolds 3 s i ∧ TaskHolds 4 s i ∧ TaskHolds 5 s i := by
  refine ⟨?_ , ?_ , ?_ ⟩
  · change decide (v31137 s i ≠ 1 ∨ v31136 s i = 1) = true
    simp [v31137, v31136, v31148, dut, reference]
  · change decide (v31150 s i ≠ 1 ∨ v31147 s i = 1) = true
    simp [v31150, v31147, v31148, dut, reference]
  · change decide (v31207 s i ≠ 1 ∨ v31205 s i = 1) = true
    simp [v31207, v31205, v31148, dut, reference]
#print axioms absent_load_tasks
theorem absent_store_tasks (s : State) (i : Inputs)
    (dut : v31215 s i = 0) (reference : v31224 s i = 0) :
    TaskHolds 6 s i ∧ TaskHolds 7 s i ∧ TaskHolds 8 s i ∧ TaskHolds 9 s i := by
  refine ⟨?_ , ?_ , ?_ , ?_ ⟩
  · change decide (v31226 s i ≠ 1 ∨ v31225 s i = 1) = true
    simp [v31226, v31225, v31233, dut, reference]
  · change decide (v31235 s i ≠ 1 ∨ v31232 s i = 1) = true
    simp [v31235, v31232, v31233, dut, reference]
  · change decide (v31304 s i ≠ 1 ∨ v31302 s i = 1) = true
    simp [v31304, v31302, v31233, dut, reference]
  · change decide (v31353 s i ≠ 1 ∨ v31351 s i = 1) = true
    simp [v31353, v31351, v31233, dut, reference]
#print axioms absent_store_tasks
theorem reference_load_opposite_zero (s : State) (i : Inputs) (operation : MemoryOp)
    (direction : operation.isLoad = true)
    (matched : v14575 s i &&& 28799 = operation.encoding.setWidth 32) :
    v31224 s i = 0 := by
  cases operation with
  | lb => exact reference_lb_opposite_event_zero s i matched
  | lh => exact reference_lh_opposite_event_zero s i matched
  | lw => exact reference_lw_opposite_event_zero s i matched
  | ld => exact reference_ld_opposite_event_zero s i matched
  | lbu => exact reference_lbu_opposite_event_zero s i matched
  | lhu => exact reference_lhu_opposite_event_zero s i matched
  | lwu => exact reference_lwu_opposite_event_zero s i matched
  | sb => simp [MemoryOp.isLoad] at direction
  | sh => simp [MemoryOp.isLoad] at direction
  | sw => simp [MemoryOp.isLoad] at direction
  | sd => simp [MemoryOp.isLoad] at direction
theorem reference_store_opposite_zero (s : State) (i : Inputs) (operation : MemoryOp)
    (direction : operation.isLoad = false)
    (matched : v14575 s i &&& 28799 = operation.encoding.setWidth 32) :
    v31135 s i = 0 := by
  cases operation with
  | lb => simp [MemoryOp.isLoad] at direction
  | lh => simp [MemoryOp.isLoad] at direction
  | lw => simp [MemoryOp.isLoad] at direction
  | ld => simp [MemoryOp.isLoad] at direction
  | lbu => simp [MemoryOp.isLoad] at direction
  | lhu => simp [MemoryOp.isLoad] at direction
  | lwu => simp [MemoryOp.isLoad] at direction
  | sb => exact reference_sb_opposite_event_zero s i matched
  | sh => exact reference_sh_opposite_event_zero s i matched
  | sw => exact reference_sw_opposite_event_zero s i matched
  | sd => exact reference_sd_opposite_event_zero s i matched
theorem committed_lsu_memory_tasks_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    ∀ task : Fin 48, 3 ≤ task.val → task.val ≤ 9 →
      TaskHolds task (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨operation, matched, _⟩ := original_assumptions_lsu_memory_run initial inputs reset environment t valid unit
  have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (28799 : BitVec 32) = operation.encoding.setWidth 32 := by
    have instruction := committed_reference_instruction _ _ _ commit
    change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
      BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
    rw [instruction]
    exact store_match_low32 operation _ matched
  cases direction : operation.isLoad with
  | true =>
    have h3 := load_valid_task3_run initial inputs reset environment t operation direction commit unit matched registers
    have h4 := load_address_task4_run initial inputs reset environment t operation direction commit unit matched registers
    have h5 := load_size_task5_run initial inputs reset environment t operation direction commit unit matched registers
    obtain ⟨h6,h7,h8,h9⟩ := absent_store_tasks _ _
      (committed_load_has_no_store_event_run initial inputs reset environment t operation direction commit unit matched)
      (reference_load_opposite_zero _ _ operation direction low)
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
  | false =>
    obtain ⟨h3,h4,h5⟩ := absent_load_tasks _ _
      (committed_store_has_no_load_event_run initial inputs reset environment t operation direction commit unit matched)
      (reference_store_opposite_zero _ _ operation direction low)
    have h6 := store_valid_task6_run initial inputs reset environment t operation direction commit unit matched registers
    have h7 := store_address_task7_run initial inputs reset environment t operation direction commit unit matched registers
    have h8 := store_data_task8_run initial inputs reset environment t operation direction commit unit matched registers
    have h9 := store_size_task9_run initial inputs reset environment t operation direction commit unit matched registers
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
#print axioms committed_lsu_memory_tasks_run
end NutShellProofs
