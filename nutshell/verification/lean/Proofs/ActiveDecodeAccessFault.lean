import Proofs.CSRInterruptRun
namespace NutShellProofs
open nNutCore

/-- The remaining active-port override is exactly the upper-seven-bit PC check. -/
theorem active_decode_override_pc_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (valid : v9827 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v28261 (run initial inputs (t + 1)) (inputs (t + 1)) =
      (if BitVec.extractLsb' 32 7
        (run initial inputs (t + 1)).g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc ≠ 0 then 1 else 0) := by
  rw [active_idu_override_sources_run initial inputs reset t valid,
    original_assumptions_decode_interrupt_zero_run initial inputs reset environment t]
  simp [v26367, v26366, v26365, v26244, v26243, v14452]

theorem active_decode_normal_iff_pc_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (valid : v9827 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v26911 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 ↔
      BitVec.extractLsb' 32 7
        (run initial inputs (t + 1)).g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc = 0 := by
  have normal : v26911 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v28261 (run initial inputs (t + 1)) (inputs (t + 1)) := rfl
  rw [normal, active_decode_override_pc_run initial inputs reset environment t valid]
  split <;> simp_all
#print axioms active_decode_override_pc_run
#print axioms active_decode_normal_iff_pc_run
end NutShellProofs
