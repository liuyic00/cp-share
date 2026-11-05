import Proofs.RetirementReferencePC
namespace NutShellProofs
open nNutCore

theorem temporary_pc32_instruction_pipeline (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    OccupiedInstructionPCPipeline (fun _ pc => BitVec.extractLsb' 32 7 pc = 0)
      (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact occupied_instruction_pc_reset _ initial (inputs 0) reset
  | succ t ih =>
    refine ⟨?_, occupied_queue_relation_step _ _ _
      (queue_occupancy_bound_run initial inputs reset t) ih.2.1 ih.1,
      occupied_exu_relation_step _ _ _ ih.2.1 ih.2.2⟩
    intro valid
    exact restriction (t + 1) valid

theorem temporary_pc32_committed_pc (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) :
    BitVec.extractLsb' 32 7 (WBUPair (run initial inputs (t + 2))).2 = 0 := by
  have capture := commit_requires_capture _ _ _ commit
  have complete : v11702 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v11702 (run initial inputs (t + 1)) (inputs (t + 1))) with idle | done
    · simp [v25332, idle] at capture
    · exact done
  have pc := (temporary_pc32_instruction_pipeline initial inputs reset restriction t).2.2
    (execute_completion_requires_valid _ _ complete)
  change BitVec.extractLsb' 32 7 (WBUPair (step (run initial inputs (t + 1)) (inputs (t + 1)))).2 = 0
  rw [committed_pair_is_execute_pair _ _ _ commit]
  exact pc

#print axioms temporary_pc32_committed_pc

theorem pc32_toNat_bound (pc : BitVec 39) (high : BitVec.extractLsb' 32 7 pc = 0) :
    pc.toNat < 2^32 := by
  have bound := pc.isLt
  have bits := congrArg BitVec.toNat high
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at bits
  omega

theorem extend_pc_small (pc : BitVec 39) (bound : pc.toNat < 2^38) :
    (extendOperandPC pc).toNat = pc.toNat := by
  have high : BitVec.extractLsb' 38 1 pc = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega
  unfold extendOperandPC
  rw [high]
  change ((0 : BitVec 25) ++ pc).toNat = pc.toNat
  rw [BitVec.toNat_append]
  simp

theorem extend_pc32_add_four (pc : BitVec 39) (high : BitVec.extractLsb' 32 7 pc = 0) :
    extendOperandPC (pc + 4) = extendOperandPC pc + 4 := by
  have bound := pc32_toNat_bound pc high
  have small : pc.toNat < 2^38 := by omega
  have add : (pc + 4).toNat = pc.toNat + 4 := by
    rw [BitVec.toNat_add]
    change (pc.toNat + 4) % 2^39 = pc.toNat + 4
    omega
  have nextSmall : (pc + 4).toNat < 2^38 := by rw [add]; omega
  apply BitVec.eq_of_toNat_eq
  rw [extend_pc_small _ nextSmall, add, BitVec.toNat_add, extend_pc_small _ small]
  change pc.toNat + 4 = (pc.toNat + 4) % 2^64
  omega

#print axioms extend_pc32_add_four
end NutShellProofs
