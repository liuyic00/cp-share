import Proofs.TemporaryJointInvariant
import Proofs.TemporaryAssertionAssembly
namespace NutShellProofs
open nNutCore

/-- All 48 original generated assertions, under the original environment plus
    the explicitly additional TemporaryIDUPC32 restriction. -/
theorem temporary_pc32_all_assertions (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : Environment initial inputs)
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    asserts (run initial inputs t) (inputs t) := by
  exact temporary_pc32_asserts_of_pc initial inputs reset environment restriction
    (temporary_pc32_task10_run initial inputs reset environment restriction) t

/-- Restricted contract only: this does not prove unfiltered CorrectAfterReset. -/
theorem correct_after_reset_with_temporary_pc32 (cycles : Nat) :
    CorrectAfterResetWithTemporaryPC32 cycles := by
  intro initial inputs reset environment restriction t
  exact temporary_pc32_all_assertions initial inputs (reset.2.1 0 reset.1)
    environment restriction t

#print axioms temporary_pc32_all_assertions
#print axioms correct_after_reset_with_temporary_pc32
end NutShellProofs
