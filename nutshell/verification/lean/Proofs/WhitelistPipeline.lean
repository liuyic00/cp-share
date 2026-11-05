import Proofs.WhitelistPredicate
import Proofs.PipelinePendingOrder
namespace NutShellProofs
open nNutCore

theorem occupied_instruction_pc_guarded_run (relation : BitVec 64 → BitVec 39 → Prop)
    (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (source : ∀ k, (inputs k).g0.nreset = 0 →
      v11102 (run initial inputs k) (inputs k) = 1 →
      relation (v11105 (run initial inputs k) (inputs k))
        (v10174 (run initial inputs k) (inputs k))) (t : Nat) :
    OccupiedInstructionPCPipeline relation (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact occupied_instruction_pc_reset relation initial (inputs 0) reset
  | succ t ih =>
    rcases BitVec.eq_zero_or_eq_one (inputs (t + 1)).g0.nreset with noReset | activeReset
    · rcases ih with ⟨idu, queue, exu⟩
      exact ⟨idu_instruction_pc_relation_step relation _ _ idu (source (t + 1) noReset),
        occupied_queue_relation_step relation _ _ (queue_occupancy_bound_run initial inputs reset t) queue idu,
        occupied_exu_relation_step relation _ _ queue exu⟩
    · exact occupied_instruction_pc_reset relation _ _ activeReset

theorem original_assumptions_whitelist_pipeline_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat) :
    OccupiedInstructionPCPipeline (fun instr _ => AllowedInstruction instr)
      (run initial inputs (t + 1)) := by
  apply occupied_instruction_pc_guarded_run _ initial inputs reset _ t
  intro k noReset capture
  have inputValid : v10100 (run initial inputs k) (inputs k) = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v10100 (run initial inputs k) (inputs k)) with idle | valid
    · simp [v11102, idle] at capture
    · exact valid
  exact original_assumptions_allowed_instruction _ _ (environment k) noReset inputValid

theorem original_assumptions_execute_allowed (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    AllowedInstruction (EXUPair (run initial inputs (t + 1))).1 := by
  exact (original_assumptions_whitelist_pipeline_run initial inputs reset environment t).2.2 valid

theorem original_assumptions_committed_allowed (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) :
    AllowedInstruction (WBUPair (run initial inputs (t + 2))).1 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have allowed := original_assumptions_execute_allowed initial inputs reset environment t valid
  have pair := committed_pair_is_execute_pair _ _ _ commit
  change WBUPair (run initial inputs (t + 2)) = EXUPair (run initial inputs (t + 1)) at pair
  rw [pair]
  exact allowed

#print axioms original_assumptions_execute_allowed
#print axioms original_assumptions_committed_allowed
end NutShellProofs
