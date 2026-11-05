import Proofs.MemoryBusyInvariant
import Proofs.MemoryDispatchPipeline
import Proofs.WhitelistFamilyCases
namespace NutShellProofs
open nNutCore

theorem original_assumptions_lsu_memory_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    ∃ op : MemoryOp, IsMemory op (EXUPair (run initial inputs (t + 1))).1 ∧
      v28 (run initial inputs (t + 1)) (inputs (t + 1)) = op.control := by
  have allowed := allowed_instruction_family _
    (original_assumptions_execute_allowed initial inputs reset environment t valid)
  obtain ⟨op, matched⟩ := (dispatch_decode_run initial inputs reset t).2 valid allowed unit
  exact ⟨op, matched, ((memory_decode_run initial inputs reset t).2 valid op matched unit).1⟩

theorem original_assumptions_memory_busy_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (busy : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0) :
    MemoryBusyFacts (run initial inputs (t + 1)) (inputs (t + 1)) := by
  apply memory_busy_facts_run initial inputs reset environment _ t busy
  intro k valid unit
  obtain ⟨op, _, control⟩ := original_assumptions_lsu_memory_run initial inputs reset environment k valid unit
  exact ⟨op, control⟩
#print axioms original_assumptions_lsu_memory_run
#print axioms original_assumptions_memory_busy_run
end NutShellProofs
