import Proofs.LoadRegisterRun
import Proofs.RegisterHold
namespace NutShellProofs
open nNutCore

/-- Every committed LSU instruction admitted by the original whitelist preserves
architectural register correspondence, including reset and misaligned accesses. -/
theorem committed_lsu_registers_preserved_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    ArchitecturalRegistersAligned (run initial inputs (t + 3)) := by
  rcases BitVec.eq_zero_or_eq_one (inputs (t + 2)).g0.nreset with currentReset | currentReset
  · have valid := commit_requires_execute_valid _ _ _ commit
    obtain ⟨operation, matched, _⟩ := original_assumptions_lsu_memory_run initial inputs reset environment t valid unit
    cases load : operation.isLoad with
    | true => exact load_registers_preserved_run initial inputs reset environment t operation load commit unit matched registers currentReset
    | false => exact store_registers_aligned_run_step initial inputs reset t operation currentReset commit unit load matched registers
  · exact registers_aligned_after_reset _ _ currentReset

/-- The LSU case also covers cycles with no commit. The unit premise is needed
only when a commit occurs; there is no assumption on alignment or instruction. -/
theorem lsu_or_idle_registers_preserved_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (unit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 →
      v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    ArchitecturalRegistersAligned (run initial inputs (t + 3)) := by
  rcases BitVec.eq_zero_or_eq_one (v9 (run initial inputs (t + 2)) (inputs (t + 2))) with idle | commit
  · rcases BitVec.eq_zero_or_eq_one (inputs (t + 2)).g0.nreset with currentReset | currentReset
    · exact registers_aligned_hold _ _ currentReset idle registers
    · exact registers_aligned_after_reset _ _ currentReset
  · exact committed_lsu_registers_preserved_run initial inputs reset environment t commit (unit commit) registers
#print axioms committed_lsu_registers_preserved_run
#print axioms lsu_or_idle_registers_preserved_run
end NutShellProofs
