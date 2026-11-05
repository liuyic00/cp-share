import Proofs.UpperPC
import Proofs.WordPC
import Proofs.ShiftPC
import Proofs.CommittedPC32
import Proofs.ImmediatePC
namespace NutShellProofs
open nNutCore

/-- Assemble a sequential commit without assuming the next PC assertion. -/
theorem temporary_pc32_reference_sequential_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (noRedirect : v14 (run initial inputs (t + 2)) (inputs (t + 2)) = 0)
    (reference : (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      (run initial inputs (t + 2)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc + 4)
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2))) :
    RetirementReferenceAligned (run initial inputs (t + 3)) := by
  have cursor := temporary_pc32_retirement_cursor_step initial inputs reset environment restriction (t + 1)
    currentReset noRedirect
  have committed := retirement_cursor_committed _ _ commit
  have high := temporary_pc32_committed_pc initial inputs reset restriction t commit
  rw [← committed] at high
  change extendOperandPC (RetirementCursor (run initial inputs (t + 2))) = _ at aligned
  unfold RetirementReferenceAligned
  rw [cursor]
  simp only [commit, ↓reduceIte]
  rw [extend_pc32_add_four _ high, aligned, reference]

theorem temporary_pc32_reference_register_alu_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) (operation : RegisterALUOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsRegisterALU operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2))) :
    RetirementReferenceAligned (run initial inputs (t + 3)) := by
  have noFlush := register_alu_commit_no_flush_run initial inputs reset environment t operation commit unit matched
  have noRedirect : v14 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 :=
    (pipeline_flush_signals _ _).2.2.symm.trans noFlush
  exact temporary_pc32_reference_sequential_commit initial inputs reset environment restriction t
    currentReset commit noRedirect
    (reference_register_alu_pc_run initial inputs t operation currentReset commit matched) aligned

#print axioms temporary_pc32_reference_register_alu_commit
theorem temporary_pc32_reference_immediate_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) (operation : ImmediateALUOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsImmediateALU operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2))) :
    RetirementReferenceAligned (run initial inputs (t + 3)) := by
  have noFlush := immediate_commit_no_flush_run initial inputs reset environment t operation commit unit matched
  have noRedirect : v14 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 :=
    (pipeline_flush_signals _ _).2.2.symm.trans noFlush
  exact temporary_pc32_reference_sequential_commit initial inputs reset environment restriction t
    currentReset commit noRedirect
    (reference_immediate_pc_run initial inputs t operation currentReset commit matched) aligned


#print axioms temporary_pc32_reference_immediate_commit
theorem temporary_pc32_reference_shift_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) (operation : ShiftImmediateOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsShiftImmediate operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2))) :
    RetirementReferenceAligned (run initial inputs (t + 3)) := by
  have noFlush := shift_commit_no_flush_run initial inputs reset environment t operation commit unit matched
  have noRedirect : v14 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 :=
    (pipeline_flush_signals _ _).2.2.symm.trans noFlush
  exact temporary_pc32_reference_sequential_commit initial inputs reset environment restriction t
    currentReset commit noRedirect
    (reference_shift_pc_run initial inputs t operation currentReset commit matched) aligned


#print axioms temporary_pc32_reference_shift_commit
theorem temporary_pc32_reference_word_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) (operation : WordImmediateOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsWordImmediate operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2))) :
    RetirementReferenceAligned (run initial inputs (t + 3)) := by
  have noFlush := word_commit_no_flush_run initial inputs reset environment t operation commit unit matched
  have noRedirect : v14 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 :=
    (pipeline_flush_signals _ _).2.2.symm.trans noFlush
  exact temporary_pc32_reference_sequential_commit initial inputs reset environment restriction t
    currentReset commit noRedirect
    (reference_word_pc_run initial inputs t operation currentReset commit matched) aligned


#print axioms temporary_pc32_reference_word_commit
theorem temporary_pc32_reference_upper_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) (operation : UpperImmediateOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsUpperImmediate operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2))) :
    RetirementReferenceAligned (run initial inputs (t + 3)) := by
  have noFlush := upper_commit_no_flush_run initial inputs reset environment t operation commit unit matched
  have noRedirect : v14 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 :=
    (pipeline_flush_signals _ _).2.2.symm.trans noFlush
  exact temporary_pc32_reference_sequential_commit initial inputs reset environment restriction t
    currentReset commit noRedirect
    (reference_upper_pc_run initial inputs t operation currentReset commit matched) aligned


#print axioms temporary_pc32_reference_upper_commit
end NutShellProofs
