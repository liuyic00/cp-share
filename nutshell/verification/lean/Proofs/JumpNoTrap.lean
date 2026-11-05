import Proofs.JumpLegalPipeline
import Proofs.LSUIdleInvariant
namespace NutShellProofs
open nNutCore
theorem jump_no_trap_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ t, assumes (run initial inputs t) (inputs t))
    (t : Nat) (operation : JumpOp)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v13725 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  have illegal := (jump_legal_run initial inputs reset t).2 valid operation matched unit
  obtain ⟨loadFault, storeFault⟩ := idle_lsu_alu_no_fault _ _ unit
    (original_assumptions_lsu_idle_run initial inputs reset environment t)
  exact alu_no_trap_remaining_sources_run initial inputs reset t valid unit illegal loadFault storeFault

#print axioms jump_no_trap_run
end NutShellProofs
