import Proofs.IdleMemoryTasks
namespace NutShellProofs
open nNutCore

theorem committed_non_lsu_masks_zero (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i ≠ 1) :
    v30865 (step s i) next = 0 ∧ v30869 (step s i) next = 0 := by
  have notLSU : v14443 s i = 0 := by
    unfold v14443
    exact if_neg unit
  constructor
  · change v25586 s i = 0
    simp [v25586, commit_requires_capture s i next commit, v25585, v25584, notLSU, v12363]
  · change v25594 s i = 0
    simp [v25594, commit_requires_capture s i next commit, v25593, v25592, notLSU, v12363]

theorem committed_non_lsu_events_zero (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i ≠ 1) :
    v31121 (step s i) next = 0 ∧ v31215 (step s i) next = 0 := by
  obtain ⟨read, write⟩ := committed_non_lsu_masks_zero s i next commit unit
  simp [v31121, v31120, v31119, v31118, v31116, v31115, v31114, read,
    v31215, v31214, v31213, v31212, v31210, v31209, v31208, write]
#print axioms committed_non_lsu_masks_zero
#print axioms committed_non_lsu_events_zero
end NutShellProofs
