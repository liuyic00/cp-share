import Proofs.WhitelistPipeline
import Proofs.WhitelistFullWidth
import Proofs.ArithmeticBits
namespace NutShellProofs
open nNutCore

/-- Full instruction width follows the real occupied pipeline, avoiding any
requirement that empty reset queue entries encode instructions. -/
theorem original_full_width_pipeline_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat) :
    OccupiedInstructionPCPipeline (fun instr _ => BitVec.extractLsb' 0 2 instr = 3)
      (run initial inputs (t + 1)) := by
  apply occupied_instruction_pc_guarded_run _ initial inputs reset _ t
  intro k noReset capture
  have valid : v10100 (run initial inputs k) (inputs k) = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v10100 (run initial inputs k) (inputs k)) with zero | one
    · simp [v11102, zero] at capture
    · exact one
  have full := original_whitelist_full_width _ _ (environment k) noReset valid
  simpa only [v30884, low_low _ (by decide : 2 ≤ 32)] using full

theorem original_execute_full_width_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    BitVec.extractLsb' 0 2 (v11547 (run initial inputs (t + 1)) (inputs (t + 1))) = 3 :=
  (original_full_width_pipeline_run initial inputs reset environment t).2.2 valid

#print axioms original_full_width_pipeline_run
#print axioms original_execute_full_width_run
end NutShellProofs
