import Proofs.RegisterALULegalPipeline
import Proofs.ReferenceRegisterALUException
import Proofs.ReferenceRegisterALU
import Proofs.BranchEventRun
namespace NutShellProofs
open nNutCore

theorem register_alu_no_trap_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : RegisterALUOp)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsRegisterALU operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v13725 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  have illegal := (register_alu_legal_run initial inputs reset t).2 valid operation matched unit
  obtain ⟨loadFault, storeFault⟩ := idle_lsu_alu_no_fault _ _ unit
    (original_assumptions_lsu_idle_run initial inputs reset environment t)
  exact alu_no_trap_remaining_sources_run initial inputs reset t valid unit illegal loadFault storeFault

theorem reference_register_alu_no_exception (s : State) (i : Inputs) (operation : RegisterALUOp)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    v23407 s i = 0 := by
  cases operation with
  | add => exact reference_register_alu_add_no_exception s i matched
  | sub => exact reference_register_alu_sub_no_exception s i matched
  | slt => exact reference_register_alu_slt_no_exception s i matched
  | sltu => exact reference_register_alu_sltu_no_exception s i matched
  | xor => exact reference_register_alu_xor_no_exception s i matched
  | or => exact reference_register_alu_or_no_exception s i matched
  | and => exact reference_register_alu_and_no_exception s i matched
  | sll => exact reference_register_alu_sll_no_exception s i matched
  | srl => exact reference_register_alu_srl_no_exception s i matched
  | sra => exact reference_register_alu_sra_no_exception s i matched

theorem register_alu_event_tasks_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : RegisterALUOp)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsRegisterALU operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
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
      (register_alu_match_low32 operation _ matched)
  have noException := reference_register_alu_no_exception _ _ operation low
  have valid := commit_requires_execute_valid
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit
  have noTrap := register_alu_no_trap_run initial inputs reset environment t operation valid unit matched
  have priorReset := (next_commit_controls
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit).1
  have actual : v31736 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 :=
    (captured_event_is_trap _ _ _ priorReset).trans noTrap
  have reference : v31739 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
    simp [v31739, v31738, v31737, v14560, v14559, v14558, commit, noException]
  exact event_tasks_when_absent _ _ actual reference

#print axioms register_alu_no_trap_run
#print axioms register_alu_event_tasks_run
end NutShellProofs
