import Proofs.StoreDataCoverage
import Proofs.MemoryReduction
namespace RiscvMiniProofs
open nCoreSoc

-- The full, unchanged generated conjunction, under only the original reset
-- and environment contract. No assertion, exclusion or extra invariant is a premise.
theorem correct_after_reset (cycles : Nat) : CorrectAfterReset cycles := by
  apply (correct_iff_store_data cycles).mpr
  intro initial inputs reset env t ht
  exact store_data_task_reachable initial inputs cycles reset env t ht

theorem original_assertions_hold (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) : asserts (run initial inputs t) (inputs t) :=
  correct_after_reset cycles initial inputs reset env t

theorem original_task_holds (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (task : Fin 45) : TaskHolds task (run initial inputs t) (inputs t) :=
  (asserts_iff_tasks _ _).mp (original_assertions_hold initial inputs cycles reset env t) task

#print axioms correct_after_reset
#print axioms original_assertions_hold
#print axioms original_task_holds
end RiscvMiniProofs
