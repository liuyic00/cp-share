import Proofs.MemoryAddressCoverage
namespace RiscvMiniProofs
open nCoreSoc

-- Every original assertion except store data, at every post-reset cycle.
theorem tasks_except_store_data_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (task : Fin 45) (other : task.val ≠ 5) :
    TaskHolds task (run initial inputs t) (inputs t) := by
  by_cases nonmemory : 7 ≤ task.val
  · exact nonmemory_tasks_reachable initial inputs cycles reset env t ht task nonmemory
  have protocol := memory_protocol_tasks_reachable initial inputs cycles reset env t ht
  have addresses := memory_address_tasks_reachable initial inputs cycles reset env t ht
  rcases protocol with ⟨readValid, readWidth, writeValid, writeWidth⟩
  rcases addresses with ⟨readAddress, writeAddress⟩
  rcases task with ⟨n, bound⟩
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 := by
    change ¬7 ≤ n at nonmemory
    change n ≠ 5 at other
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact readValid
  · exact readAddress
  · exact readWidth
  · exact writeValid
  · exact writeAddress
  · exact writeWidth

-- The full unchanged target now has exactly one outstanding original task.
theorem correct_iff_store_data (cycles : Nat) :
    CorrectAfterReset cycles ↔
      ∀ (initial : State) (inputs : Nat → Inputs),
        ResetPrefix inputs cycles → Environment initial inputs →
          ∀ t, cycles ≤ t → TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  constructor
  · intro correct initial inputs reset env t _
    exact (asserts_iff_tasks _ _).mp (correct initial inputs reset env t) ⟨5, by decide⟩
  · intro data
    apply lift_after_reset
    intro initial inputs reset env t ht
    apply (asserts_iff_tasks _ _).mpr
    intro task
    by_cases store : task.val = 5
    · have eq : task = ⟨5, by decide⟩ := Fin.ext store
      subst task
      exact data initial inputs reset env t ht
    · exact tasks_except_store_data_reachable initial inputs cycles reset env t ht task store

#print axioms tasks_except_store_data_reachable
#print axioms correct_iff_store_data
end RiscvMiniProofs
