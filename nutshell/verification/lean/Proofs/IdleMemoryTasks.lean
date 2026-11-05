import Proofs.CommittedMemoryTasks
namespace NutShellProofs
open nNutCore

theorem no_commit_memory_events (s : State) (i : Inputs) (idle : v9 s i = 0) :
    v31121 s i = 0 ∧ v31135 s i = 0 ∧ v31215 s i = 0 ∧ v31224 s i = 0 := by
  simp [v31121, v31120, v31119, v31118, v31116, v30709, v30708, v30707,
    v31135, v31134, v31133, v14560, v14559, v14558, idle, v24,
    v31215, v31214, v31213, v31212, v31210, v31224, v31223, v31222]

theorem no_commit_memory_tasks (s : State) (i : Inputs) (idle : v9 s i = 0) :
    ∀ task : Fin 48, 3 ≤ task.val → task.val ≤ 9 → TaskHolds task s i := by
  obtain ⟨dl, rl, ds, rs⟩ := no_commit_memory_events s i idle
  obtain ⟨h3,h4,h5⟩ := absent_load_tasks s i dl rl
  obtain ⟨h6,h7,h8,h9⟩ := absent_store_tasks s i ds rs
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
#print axioms no_commit_memory_events
#print axioms no_commit_memory_tasks
end NutShellProofs
