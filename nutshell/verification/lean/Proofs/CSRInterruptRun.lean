import Proofs.CSRInterruptEnable
import Proofs.WhitelistCSRPipeline
import Proofs.WhitelistFamilyCases
import Proofs.WhitelistPipeline
namespace NutShellProofs
open nNutCore

theorem original_assumptions_csr_write_coverage (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat) :
    v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 ∨
    v3 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 3 ∨
    v28 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  rcases BitVec.eq_zero_or_eq_one (v6 (run initial inputs (t + 1)) (inputs (t + 1))) with idle | valid
  · exact Or.inl idle
  · by_cases csr : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 3
    · have allowed := allowed_instruction_family _
        (original_assumptions_execute_allowed initial inputs reset environment t valid)
      exact Or.inr (Or.inr ((csr_control_decode_run initial inputs reset t).2 valid allowed csr))
    · exact Or.inr (Or.inl csr)

theorem original_assumptions_mie_zero_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat) :
    (run initial inputs (t + 1)).g43.r1378_nbackend_5Fexu_5Fcsr_5Fmie = 0 := by
  exact csr_mie_zero_run initial inputs reset
    (original_assumptions_csr_write_coverage initial inputs reset environment) t

theorem original_assumptions_decode_interrupt_zero_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat) :
    v10039 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  exact csr_mie_zero_disables_interrupt _ _
    (original_assumptions_mie_zero_run initial inputs reset environment t)
#print axioms original_assumptions_mie_zero_run
#print axioms original_assumptions_decode_interrupt_zero_run
end NutShellProofs
