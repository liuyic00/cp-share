import Proofs.TemporaryRegisterInvariant
import Proofs.Assembly
namespace NutShellProofs
open nNutCore
theorem register_task_when_idle (s : State) (i : Inputs) (idle : v9 s i = 0)
    (task : Fin 48) (lo : 12 ≤ task.val) (hi : task.val ≤ 42) : TaskHolds task s i := by
  have cases : task = 12 ∨ task = 13 ∨ task = 14 ∨ task = 15 ∨ task = 16 ∨ task = 17 ∨ task = 18 ∨ task = 19 ∨ task = 20 ∨ task = 21 ∨ task = 22 ∨ task = 23 ∨ task = 24 ∨ task = 25 ∨ task = 26 ∨ task = 27 ∨ task = 28 ∨ task = 29 ∨ task = 30 ∨ task = 31 ∨ task = 32 ∨ task = 33 ∨ task = 34 ∨ task = 35 ∨ task = 36 ∨ task = 37 ∨ task = 38 ∨ task = 39 ∨ task = 40 ∨ task = 41 ∨ task = 42 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change decide (v31388 s i ≠ 1 ∨ v31386 s i = 1) = true
    simp [v31388, v14558, idle]
  · change decide (v31400 s i ≠ 1 ∨ v31398 s i = 1) = true
    simp [v31400, v14558, idle]
  · change decide (v31412 s i ≠ 1 ∨ v31410 s i = 1) = true
    simp [v31412, v14558, idle]
  · change decide (v31424 s i ≠ 1 ∨ v31422 s i = 1) = true
    simp [v31424, v14558, idle]
  · change decide (v31436 s i ≠ 1 ∨ v31434 s i = 1) = true
    simp [v31436, v14558, idle]
  · change decide (v31448 s i ≠ 1 ∨ v31446 s i = 1) = true
    simp [v31448, v14558, idle]
  · change decide (v31460 s i ≠ 1 ∨ v31458 s i = 1) = true
    simp [v31460, v14558, idle]
  · change decide (v31472 s i ≠ 1 ∨ v31470 s i = 1) = true
    simp [v31472, v14558, idle]
  · change decide (v31484 s i ≠ 1 ∨ v31482 s i = 1) = true
    simp [v31484, v14558, idle]
  · change decide (v31496 s i ≠ 1 ∨ v31494 s i = 1) = true
    simp [v31496, v14558, idle]
  · change decide (v31508 s i ≠ 1 ∨ v31506 s i = 1) = true
    simp [v31508, v14558, idle]
  · change decide (v31520 s i ≠ 1 ∨ v31518 s i = 1) = true
    simp [v31520, v14558, idle]
  · change decide (v31532 s i ≠ 1 ∨ v31530 s i = 1) = true
    simp [v31532, v14558, idle]
  · change decide (v31544 s i ≠ 1 ∨ v31542 s i = 1) = true
    simp [v31544, v14558, idle]
  · change decide (v31556 s i ≠ 1 ∨ v31554 s i = 1) = true
    simp [v31556, v14558, idle]
  · change decide (v31567 s i ≠ 1 ∨ v31565 s i = 1) = true
    simp [v31567, v14558, idle]
  · change decide (v31578 s i ≠ 1 ∨ v31576 s i = 1) = true
    simp [v31578, v14558, idle]
  · change decide (v31589 s i ≠ 1 ∨ v31587 s i = 1) = true
    simp [v31589, v14558, idle]
  · change decide (v31600 s i ≠ 1 ∨ v31598 s i = 1) = true
    simp [v31600, v14558, idle]
  · change decide (v31611 s i ≠ 1 ∨ v31609 s i = 1) = true
    simp [v31611, v14558, idle]
  · change decide (v31622 s i ≠ 1 ∨ v31620 s i = 1) = true
    simp [v31622, v14558, idle]
  · change decide (v31633 s i ≠ 1 ∨ v31631 s i = 1) = true
    simp [v31633, v14558, idle]
  · change decide (v31644 s i ≠ 1 ∨ v31642 s i = 1) = true
    simp [v31644, v14558, idle]
  · change decide (v31655 s i ≠ 1 ∨ v31653 s i = 1) = true
    simp [v31655, v14558, idle]
  · change decide (v31666 s i ≠ 1 ∨ v31664 s i = 1) = true
    simp [v31666, v14558, idle]
  · change decide (v31677 s i ≠ 1 ∨ v31675 s i = 1) = true
    simp [v31677, v14558, idle]
  · change decide (v31688 s i ≠ 1 ∨ v31686 s i = 1) = true
    simp [v31688, v14558, idle]
  · change decide (v31699 s i ≠ 1 ∨ v31697 s i = 1) = true
    simp [v31699, v14558, idle]
  · change decide (v31710 s i ≠ 1 ∨ v31708 s i = 1) = true
    simp [v31710, v14558, idle]
  · change decide (v31721 s i ≠ 1 ∨ v31719 s i = 1) = true
    simp [v31721, v14558, idle]
  · change decide (v31732 s i ≠ 1 ∨ v31730 s i = 1) = true
    simp [v31732, v14558, idle]

theorem register_tasks_index (s : State) (i : Inputs) (tasks : RegisterTasks s i)
    (task : Fin 48) (lo : 12 ≤ task.val) (hi : task.val ≤ 42) : TaskHolds task s i := by
  have cases : task = 12 ∨ task = 13 ∨ task = 14 ∨ task = 15 ∨ task = 16 ∨ task = 17 ∨ task = 18 ∨ task = 19 ∨ task = 20 ∨ task = 21 ∨ task = 22 ∨ task = 23 ∨ task = 24 ∨ task = 25 ∨ task = 26 ∨ task = 27 ∨ task = 28 ∨ task = 29 ∨ task = 30 ∨ task = 31 ∨ task = 32 ∨ task = 33 ∨ task = 34 ∨ task = 35 ∨ task = 36 ∨ task = 37 ∨ task = 38 ∨ task = 39 ∨ task = 40 ∨ task = 41 ∨ task = 42 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all only [RegisterTasks]

theorem temporary_pc32_register_tasks_run_of_pc (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs)
    (pc : ∀ k, TaskHolds 10 (run initial inputs (k + 2)) (inputs (k + 2)))
    (t : Nat) (task : Fin 48) (lo : 12 ≤ task.val) (hi : task.val ≤ 42) :
    TaskHolds task (run initial inputs t) (inputs t) := by
  rcases BitVec.eq_zero_or_eq_one (inputs t).g0.nreset with currentReset | currentReset
  · rcases BitVec.eq_zero_or_eq_one (v9 (run initial inputs t) (inputs t)) with idle | commit
    · exact register_task_when_idle _ _ idle task lo hi
    · exact register_tasks_index _ _
        (temporary_pc32_committed_register_tasks_of_pc initial inputs reset environment restriction pc t currentReset commit) task lo hi
  · exact (asserts_iff_tasks _ _).mp (assertions_during_reset _ _ currentReset) task
#print axioms register_task_when_idle
#print axioms temporary_pc32_register_tasks_run_of_pc
end NutShellProofs
