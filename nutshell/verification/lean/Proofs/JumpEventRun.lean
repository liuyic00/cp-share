import Proofs.JumpNoTrap
import Proofs.ReferenceJumpAlignment
import Proofs.BranchEventRun
namespace NutShellProofs
open nNutCore

theorem jal_event_tasks_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jal (EXUPair (run initial inputs (t + 1))).1)
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    TaskHolds 43 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 44 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 45 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 46 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 47 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have mask : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (127 : BitVec 32) = 111 := by
    have instruction := committed_reference_instruction _ _ _ commit
    change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
      BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
    rw [instruction]
    exact jump_match_low32 .jal _ matched
  have ok := reference_jump_jal_alignment _ _
    (jal_reference_sum_aligned_run initial inputs reset t (environment (t + 1)) currentReset commit unit matched pc)
  have noException := reference_jump_jal_no_exception _ _ mask ok
  have noTrap := jump_no_trap_run initial inputs reset environment t .jal
    (commit_requires_execute_valid _ _ _ commit) unit matched
  have actual : v31736 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 :=
    (captured_event_is_trap _ _ _ (next_commit_controls _ _ _ commit).1).trans noTrap
  have reference : v31739 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
    simp [v31739, v31738, v31737, v14560, v14559, v14558, commit, noException]
  exact event_tasks_when_absent _ _ actual reference
#print axioms jal_event_tasks_run

theorem jalr_event_tasks_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jalr (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    TaskHolds 43 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 44 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 45 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 46 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 47 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have mask : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (28799 : BitVec 32) = 103 := by
    have instruction := committed_reference_instruction _ _ _ commit
    change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
      BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
    rw [instruction]
    exact jump_match_low32 .jalr _ matched
  have ok := reference_jump_jalr_alignment _ _
    (jalr_reference_sum_aligned_run initial inputs reset t (environment (t + 1)) commit unit matched aligned)
  have noException := reference_jump_jalr_no_exception _ _ mask ok
  have noTrap := jump_no_trap_run initial inputs reset environment t .jalr
    (commit_requires_execute_valid _ _ _ commit) unit matched
  have actual : v31736 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 :=
    (captured_event_is_trap _ _ _ (next_commit_controls _ _ _ commit).1).trans noTrap
  have reference : v31739 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
    simp [v31739, v31738, v31737, v14560, v14559, v14558, commit, noException]
  exact event_tasks_when_absent _ _ actual reference
#print axioms jalr_event_tasks_run
end NutShellProofs
