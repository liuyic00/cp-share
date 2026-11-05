import Proofs.WhitelistFullWidth
import Proofs.ArithmeticBits
namespace NutShellProofs
open nNutCore

theorem original_assumptions_disable_compressed_output (s : State) (i : Inputs)
    (environment : assumes s i) (reset : i.g0.nreset = 0) (valid : v10100 s i = 1) :
    v9780 s i = 0 := by
  have full := original_whitelist_full_width s i environment reset valid
  have instruction : v30884 s i = v9778 s i := by
    simp [v30884, v11105, v11104,
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 32 ≤ 32)]
  rw [instruction] at full
  have bits : v9779 s i = v2750 s i := full
  exact if_neg (not_not_intro bits)

/-- The normal sequential instruction address uses four bytes on the allowed output. -/
theorem original_assumptions_instruction_pc_plus_four (s : State) (i : Inputs)
    (environment : assumes s i) (reset : i.g0.nreset = 0) (valid : v10100 s i = 1) :
    v11118 s i = v9733 s i + 4 := by
  have full := original_assumptions_disable_compressed_output s i environment reset valid
  simp [v11118, full, v11117, v11116, v11114, v11115,
    low_add _ _ (by decide : 39 ≤ 40),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 39)]

/-- IDU captures the instruction and associated buffer output PC on the same handshake. -/
theorem idu_instruction_pc_capture (s : State) (i : Inputs) (capture : v11102 s i = 1) :
    (step s i).g38.r1242_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Finstr = v11105 s i ∧
    (step s i).g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc = v10174 s i := by
  constructor
  · change v11106 s i = _
    simp [v11106, capture]
  · change v11108 s i = _
    simp [v11108, capture, v11107]

theorem idu_instruction_pc_hold (s : State) (i : Inputs) (noCapture : v11102 s i ≠ 1) :
    (step s i).g38.r1242_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Finstr =
      s.g38.r1242_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Finstr ∧
    (step s i).g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc =
      s.g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc := by
  constructor
  · change v11106 s i = _
    exact if_neg noCapture
  · change v11108 s i = _
    exact if_neg noCapture

#print axioms original_assumptions_disable_compressed_output
#print axioms original_assumptions_instruction_pc_plus_four
#print axioms idu_instruction_pc_capture
#print axioms idu_instruction_pc_hold
end NutShellProofs
