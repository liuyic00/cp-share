import Proofs.LoadAddressTask
namespace NutShellProofs
open nNutCore

theorem memory_address_latched_incomplete_step_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat)
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (incomplete : v11702 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 1)
    (latched : MemoryAddressLatched (run initial inputs (t + 1)) (inputs (t + 1))) :
    MemoryAddressLatched (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have hold : v24283 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 1 := by
    intro capture
    exact incomplete (execute_capture_replaces_only_completed _ _ valid capture)
  exact memory_address_latched_hold _ _ _ currentReset unit
    (original_assumptions_lsu_idle_run initial inputs reset environment t)
    (original_assumptions_lsu_idle_run initial inputs reset environment (t + 1)) hold latched

theorem memory_address_latched_wait_interval (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (start count : Nat)
    (latched : MemoryAddressLatched (run initial inputs (start + 1)) (inputs (start + 1)))
    (waiting : ∀ k, k < count →
      (inputs (start + k + 1)).g0.nreset = 0 ∧
      v3 (run initial inputs (start + k + 1)) (inputs (start + k + 1)) = 1 ∧
      v6 (run initial inputs (start + k + 1)) (inputs (start + k + 1)) = 1 ∧
      v11702 (run initial inputs (start + k + 1)) (inputs (start + k + 1)) ≠ 1) :
    MemoryAddressLatched (run initial inputs (start + count + 1)) (inputs (start + count + 1)) := by
  induction count with
  | zero => simpa using latched
  | succ count ih =>
    have prior := ih (fun k hk => waiting k (by omega))
    obtain ⟨noReset, unit, valid, incomplete⟩ := waiting count (by omega)
    have next := memory_address_latched_incomplete_step_run initial inputs reset environment
      (start + count) noReset unit valid incomplete prior
    simpa only [Nat.add_assoc] using next
#print axioms memory_address_latched_incomplete_step_run
#print axioms memory_address_latched_wait_interval
end NutShellProofs
