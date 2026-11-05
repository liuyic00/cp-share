import Proofs.MemoryInterruptSignal
import Proofs.MemoryTrapCorrespondence
namespace NutShellProofs
open nNutCore

/-- The recorded interrupt number is zero when no interrupt was selected. -/
theorem no_interrupt_event_number (s : State) (i next : Inputs)
    (noInterrupt : v13720 s i = 0) : v31748 (step s i) next = 0 := by
  change (v13727 (step s i) next ++ v14416 s i) = 0
  unfold v13727 v14416 v14415 v14414 v14413
  simp only [HAppend.hAppend, BitVec.instHAppendHAddNat, BitVec.append, BitVec.shiftLeftZeroExtend]
  simp [noInterrupt]

theorem zero_interrupt_number_task44 (s : State) (i : Inputs)
    (number : v31748 s i = 0) : TaskHolds 44 s i := by
  change decide (_ ≠ 1 ∨ v31751 s i = 1) = true
  simp [v31751, v31750, v31749, v4051, number]

/-- Original interrupt-number assertion for LSU commits, including exceptions. -/
theorem committed_lsu_event_task44_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    TaskHolds 44 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have noInterrupt := memory_interrupt_signal_run initial inputs reset t valid unit
  exact zero_interrupt_number_task44 _ _ (no_interrupt_event_number _ _ _ noInterrupt)
#print axioms no_interrupt_event_number
#print axioms zero_interrupt_number_task44
#print axioms committed_lsu_event_task44_run
end NutShellProofs
