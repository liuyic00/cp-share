import Proofs.TemporaryRegisterStep
import Proofs.RegisterBridge
namespace NutShellProofs
open nNutCore

theorem reset_has_no_next_commit (s : State) (i next : Inputs)
    (reset : i.g0.nreset = 1) : v9 (step s i) next = 0 := by
  change v25331 s i = 0
  simp [v25331, v11455, reset, v24]

/-- Register correspondence at every post-reset cycle, conditional on the
still-outstanding PC invariant. This is not a proof of the full contract. -/
theorem temporary_pc32_registers_run_of_pc (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs)
    (pc : ∀ k, TaskHolds 10 (run initial inputs (k + 2)) (inputs (k + 2)))
    (t : Nat) : ArchitecturalRegistersAligned (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact registers_aligned_after_reset _ _ reset
  | succ t ih =>
    cases t with
    | zero =>
      have idle : v9 (run initial inputs 1) (inputs 1) = 0 := reset_has_no_next_commit _ _ _ reset
      rcases BitVec.eq_zero_or_eq_one (inputs 1).g0.nreset with currentReset | currentReset
      · exact registers_aligned_hold _ _ currentReset idle ih
      · exact registers_aligned_after_reset _ _ currentReset
    | succ t =>
      exact temporary_pc32_registers_preserved_step initial inputs reset environment restriction t ih (pc t)
#print axioms reset_has_no_next_commit
#print axioms temporary_pc32_registers_run_of_pc
/-- The invariant proves the original generated register assertions on commits,
not merely an auxiliary relation between abstract register files. -/
theorem temporary_pc32_committed_register_tasks_of_pc (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs)
    (pc : ∀ k, TaskHolds 10 (run initial inputs (k + 2)) (inputs (k + 2)))
    (t : Nat) (currentReset : (inputs t).g0.nreset = 0)
    (commit : v9 (run initial inputs t) (inputs t) = 1) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  apply (register_commit_iff _ _ currentReset commit).mpr
  exact temporary_pc32_registers_run_of_pc initial inputs reset environment restriction pc t
#print axioms temporary_pc32_committed_register_tasks_of_pc
end NutShellProofs
