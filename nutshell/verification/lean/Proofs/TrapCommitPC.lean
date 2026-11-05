import Proofs.ReferenceTrapPC
import Proofs.CommittedPC32
import Proofs.TrapRedirect
namespace NutShellProofs
open nNutCore

theorem temporary_pc32_reference_trap_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (trap : v13725 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (exception : v23407 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) :
    RetirementReferenceAligned (run initial inputs (t + 3)) := by
  have flush := committed_trap_flushes_next _ _ _ commit trap
  have redirect : v14 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 :=
    (pipeline_flush_signals _ _).2.2.symm.trans flush
  have target := temporary_pc32_committed_trap_target_zero_run initial inputs reset environment restriction t commit trap
  have cursor := retirement_cursor_redirect (run initial inputs (t + 2)) (inputs (t + 2)) currentReset redirect
  change RetirementCursor (run initial inputs (t + 3)) = _ at cursor
  have reference := reference_exception_pc_zero (run initial inputs (t + 2)) (inputs (t + 2))
    currentReset commit exception (reference_trap_vectors_run initial inputs reset (t + 1))
    (reference_mxlen_run initial inputs reset (t + 1))
  change (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc = 0 at reference
  unfold RetirementReferenceAligned
  rw [cursor, target, reference]
  simp [extendOperandPC]

#print axioms temporary_pc32_reference_trap_commit
end NutShellProofs
