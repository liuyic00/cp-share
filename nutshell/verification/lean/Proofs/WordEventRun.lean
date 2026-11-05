import Proofs.WordNoTrap
import Proofs.ReferenceWordException
import Proofs.ReferenceWord
import Proofs.BranchEventRun
namespace NutShellProofs
open nNutCore

theorem reference_word_no_exception (s : State) (i : Inputs) (operation : WordImmediateOp)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    v23407 s i = 0 := by
  cases operation with
  | add => exact reference_word_add_no_exception s i matched
  | sll => exact reference_word_sll_no_exception s i matched
  | srl => exact reference_word_srl_no_exception s i matched
  | sra => exact reference_word_sra_no_exception s i matched

theorem word_event_tasks_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : WordImmediateOp)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsWordImmediate operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    TaskHolds 43 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 44 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 45 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 46 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 47 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have instr := committed_reference_instruction
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit
  have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&&
      operation.mask.setWidth 32 = operation.encoding.setWidth 32 :=
    (congrArg (fun x => x &&& operation.mask.setWidth 32) instr).trans
      (word_match_low32 operation _ matched)
  have noException := reference_word_no_exception _ _ operation low
  have valid := commit_requires_execute_valid
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit
  have noTrap := word_no_trap_run initial inputs reset environment t operation valid unit matched
  have priorReset := (next_commit_controls
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit).1
  have actual : v31736 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 :=
    (captured_event_is_trap _ _ _ priorReset).trans noTrap
  have reference : v31739 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
    simp [v31739, v31738, v31737, v14560, v14559, v14558, commit, noException]
  exact event_tasks_when_absent _ _ actual reference


#print axioms word_event_tasks_run
end NutShellProofs
