import Proofs.ShiftLegalPipeline
import Proofs.LSUIdleInvariant
namespace NutShellProofs
open nNutCore
theorem shift_no_trap_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : ShiftImmediateOp)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsShiftImmediate operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v13725 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  have illegal := (shift_legal_run initial inputs reset t).2 valid operation matched unit
  obtain ⟨loadFault, storeFault⟩ := idle_lsu_alu_no_fault _ _ unit
    (original_assumptions_lsu_idle_run initial inputs reset environment t)
  exact alu_no_trap_remaining_sources_run initial inputs reset t valid unit illegal loadFault storeFault

#print axioms shift_no_trap_run
end NutShellProofs
