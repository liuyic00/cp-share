import Proofs.Contract

namespace RiscvMiniProofs
open nCoreSoc

private theorem bit_cases (b : BitVec 1) : b = 0 ∨ b = 1 := by
  by_cases h : b.toNat = 0
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · right
    apply BitVec.eq_of_toNat_eq
    have := b.isLt
    change b.toNat = 1
    omega

-- Both interrupt-number wires are tied to the same zero constant.
theorem event_interrupt_number_task (s : State) (i : Inputs) :
    TaskHolds ⟨41, by decide⟩ s i := by
  change decide (v9593 s i ≠ 1 ∨ v9591 s i = 1) = true
  simp [v9591, v9588, v9590, v9587, v9589]

-- Once event validity agrees, the instruction payload is the same committed
-- instruction. This is a dependency between two ORIGINAL generated tasks.
theorem event_instruction_of_validity (s : State) (i : Inputs)
    (valid : TaskHolds ⟨40, by decide⟩ s i) :
    TaskHolds ⟨44, by decide⟩ s i := by
  change decide (v9586 s i ≠ 1 ∨ v9583 s i = 1) = true at valid
  change decide (v9624 s i ≠ 1 ∨ v9622 s i = 1) = true
  rcases bit_cases (v182 s i) with hD | hD <;>
    rcases bit_cases (v964 s i) with hC | hC <;>
    rcases bit_cases (v6727 s i) with hE | hE <;>
    rcases bit_cases (v955 s i) with hR | hR <;>
    simp_all [v9586, v9584, v9585, v9583, v9579, v9578, v9582, v9581,
      v9580, v9624, v9623, v9622, v9617, v9616, v9621, v9620, v9619,
      v9618, v977, v975, v974, v973, v53, v4]

-- The original environment excludes DUT traps. If validity agrees as well,
-- neither side raises an event, so all event-payload enables are zero.
theorem event_payloads_of_validity (s : State) (i : Inputs)
    (env : assumes s i) (valid : TaskHolds ⟨40, by decide⟩ s i) :
    TaskHolds ⟨42, by decide⟩ s i ∧ TaskHolds ⟨43, by decide⟩ s i := by
  simp only [assumes, eval, assumptionChecks, assumptionChecks0, List.flatten, List.append_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq, decide_eq_true_eq] at env
  change decide (v9586 s i ≠ 1 ∨ v9583 s i = 1) = true at valid
  change (decide (v9604 s i ≠ 1 ∨ v9602 s i = 1) = true) ∧
    (decide (v9615 s i ≠ 1 ∨ v9613 s i = 1) = true)
  rcases bit_cases (v182 s i) with hD | hD <;>
    rcases bit_cases (v9582 s i) with hE | hE <;>
    rcases bit_cases (v9797 s i) with hA | hA <;>
    rcases bit_cases i.nreset with hR | hR <;>
    simp_all [v9801, v9800, v9799, v9798, v8625, v8624, v8623,
      v9586, v9584, v9585, v9583, v9579, v9578,
      v9604, v9603, v9615, v9614, v955, v1, v0, v4]

#print axioms event_payloads_of_validity
#print axioms event_interrupt_number_task
#print axioms event_instruction_of_validity
end RiscvMiniProofs
