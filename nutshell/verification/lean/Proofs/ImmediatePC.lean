import Proofs.ImmediateEventRun
import Proofs.ImmediatePipeline
import Proofs.ReferenceImmediateRedirect
namespace NutShellProofs
open nNutCore

theorem reference_immediate_pc_step (s : State) (i : Inputs) (operation : ImmediateALUOp)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (BitVec.ofNat 32 28799) = operation.encoding.setWidth 32) :
    (step s i).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc = v16457 s i + 4 := by
  have noException := reference_immediate_no_exception s i operation matched
  cases operation with
  | add =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_immediate_add_not_v14595 s i matched)
      (reference_immediate_add_not_v14601 s i matched),
      reference_immediate_add_no_redirect s i matched]
    rfl

  | slt =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_immediate_slt_not_v14595 s i matched)
      (reference_immediate_slt_not_v14601 s i matched),
      reference_immediate_slt_no_redirect s i matched]
    rfl
  | sltu =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_immediate_sltu_not_v14595 s i matched)
      (reference_immediate_sltu_not_v14601 s i matched),
      reference_immediate_sltu_no_redirect s i matched]
    rfl
  | xor =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_immediate_xor_not_v14595 s i matched)
      (reference_immediate_xor_not_v14601 s i matched),
      reference_immediate_xor_no_redirect s i matched]
    rfl
  | or =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_immediate_or_not_v14595 s i matched)
      (reference_immediate_or_not_v14601 s i matched),
      reference_immediate_or_no_redirect s i matched]
    rfl
  | and =>
    rw [reference_pc_update_normal s i reset commit noException
      (reference_immediate_and_not_v14595 s i matched)
      (reference_immediate_and_not_v14601 s i matched),
      reference_immediate_and_no_redirect s i matched]
    rfl




theorem immediate_redirect_disabled (s : State) (i : Inputs) (operation : ImmediateALUOp)
    (unit : v3 s i = 0) (op : v28 s i = operation.control) (noTrap : v13725 s i = 0) :
    v25387 s i = 0 := by
  obtain ⟨mou, csr⟩ := alu_redirect_priority s i unit
  have noCSR := csr.trans noTrap
  have branchBit : v12142 s i = 0 := by
    cases operation <;> simp [v12142, v12141, op, ImmediateALUOp.control]
  simp [v25387, v25386, mou, v25385, noCSR, v25384, v25383, v25382, branchBit]

theorem immediate_commit_no_flush_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : ImmediateALUOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsImmediateALU operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v23 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
  have valid := commit_requires_execute_valid
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit
  obtain ⟨op, _, _, _⟩ :=
    (immediate_decode_run initial inputs reset t).2 valid operation matched unit
  have noTrap := immediate_no_trap_run initial inputs reset environment t operation valid unit matched
  have noRedirect := immediate_redirect_disabled
    (run initial inputs (t + 1)) (inputs (t + 1)) operation unit op noTrap
  have captured : v8 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
    change v25388 (run initial inputs (t + 1)) (inputs (t + 1)) = 0
    rw [v25388, if_pos (commit_requires_capture _ _ _ commit), noRedirect]
  exact (commit_flush_eq_redirect _ _ commit).trans captured


theorem reference_immediate_pc_run (initial : State) (inputs : Nat → Inputs)
    (t : Nat) (operation : ImmediateALUOp)
    (reset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (matched : IsImmediateALU operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      v16457 (run initial inputs (t + 2)) (inputs (t + 2)) + 4 := by
  have instr := committed_reference_instruction
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit
  have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&&
      (BitVec.ofNat 32 28799) = operation.encoding.setWidth 32 :=
    (congrArg (fun x => x &&& (BitVec.ofNat 32 28799)) instr).trans
      (immediate_match_low32 operation _ matched)
  exact reference_immediate_pc_step _ _ operation reset commit low

#print axioms reference_immediate_pc_run
#print axioms reference_immediate_pc_step
#print axioms immediate_commit_no_flush_run
end NutShellProofs
