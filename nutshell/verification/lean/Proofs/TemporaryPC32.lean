import Proofs.ActiveDecodeAccessFault
import Proofs.WhitelistNormalUnit
namespace NutShellProofs
open nNutCore

/-- Temporary additional restriction prompted by counterexamples/jalr-4g.json.
Not derived from the original assumptions. Excludes high-PC valid IDU instructions,
including speculative valid instructions. The original contract remains unchanged. -/
def TemporaryIDUPC32 (initial : State) (inputs : Nat → Inputs) : Prop :=
  ∀ t, v9827 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 →
    BitVec.extractLsb' 32 7
      (run initial inputs (t + 1)).g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc = 0

/-- Restricted contract, proved in Proofs.TemporaryCorrectness.
This definition itself does not assert unrestricted correctness. -/
def CorrectAfterResetWithTemporaryPC32 (cycles : Nat) : Prop :=
  ∀ (initial : State) (inputs : Nat → Inputs),
    ResetPrefix inputs cycles → Environment initial inputs →
      TemporaryIDUPC32 initial inputs → ∀ t, asserts (run initial inputs t) (inputs t)

theorem temporary_pc32_active_decode_normal (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (valid : v9827 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v26911 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  exact (active_decode_normal_iff_pc_run initial inputs reset environment t valid).mpr
    (restriction t valid)

theorem temporary_pc32_allowed_active_decode_noncsr (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (valid : v9827 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (allowed : AllowedInstructionFamily (v26223 (run initial inputs (t + 1)) (inputs (t + 1)))) :
    v28438 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 3 := by
  exact normal_allowed_idu_noncsr _ _
    (temporary_pc32_active_decode_normal initial inputs reset environment restriction t valid) allowed
#print axioms temporary_pc32_active_decode_normal
#print axioms temporary_pc32_allowed_active_decode_noncsr
theorem temporary_pc32_active_decode_noncsr (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (valid : v9827 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v28438 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 3 := by
  have allowed := (original_assumptions_whitelist_pipeline_run initial inputs reset environment t).1 valid
  exact temporary_pc32_allowed_active_decode_noncsr initial inputs reset environment restriction t valid
    (allowed_instruction_family _ allowed)
#print axioms temporary_pc32_active_decode_noncsr
end NutShellProofs
