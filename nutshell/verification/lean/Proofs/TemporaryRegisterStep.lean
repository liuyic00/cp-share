import Proofs.ALULSUPipeline
import Proofs.ALURegisterRun
import Proofs.LSURegisterRun
namespace NutShellProofs
open nNutCore

/-- Unit coverage under the explicitly additional temporary high-PC restriction. -/
theorem temporary_pc32_execute_alulsu (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 ∨
      v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 := by
  have source : ∀ k, v9827 (run initial inputs (k + 1)) (inputs (k + 1)) = 1 →
      ALULSU (v28438 (run initial inputs (k + 1)) (inputs (k + 1))) := by
    intro k active
    exact normal_allowed_idu_alulsu _ _
      (temporary_pc32_active_decode_normal initial inputs reset environment restriction k active)
      (allowed_instruction_family _ ((original_assumptions_whitelist_pipeline_run initial inputs reset environment k).1 active))
  exact (alulsu_decode_run initial inputs reset source t).2 valid

/-- Full instruction-case register preservation. The global PC and register
induction hypotheses remain explicit, as does the temporary PC restriction. -/
theorem temporary_pc32_registers_preserved_step (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    ArchitecturalRegistersAligned (run initial inputs (t + 3)) := by
  rcases BitVec.eq_zero_or_eq_one (v9 (run initial inputs (t + 2)) (inputs (t + 2))) with idle | commit
  · rcases BitVec.eq_zero_or_eq_one (inputs (t + 2)).g0.nreset with currentReset | currentReset
    · exact registers_aligned_hold _ _ currentReset idle registers
    · exact registers_aligned_after_reset _ _ currentReset
  · have valid := commit_requires_execute_valid _ _ _ commit
    rcases temporary_pc32_execute_alulsu initial inputs reset environment restriction t valid with alu | lsu
    · exact committed_alu_registers_preserved_run initial inputs reset environment t commit alu registers pc
    · exact committed_lsu_registers_preserved_run initial inputs reset environment t commit lsu registers
#print axioms temporary_pc32_execute_alulsu
#print axioms temporary_pc32_registers_preserved_step
end NutShellProofs
