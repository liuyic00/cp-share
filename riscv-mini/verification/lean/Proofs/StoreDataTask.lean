import Proofs.MemoryProtocol
namespace RiscvMiniProofs
open nCoreSoc

theorem store_data_task_of_equality (s : State) (i : Inputs)
    (data : v9237 s i = v9249 s i) : TaskHolds ⟨5, by decide⟩ s i := by
  change decide (v9252 s i ≠ 1 ∨ v9250 s i = 1) = true
  simp [v9250, data]

theorem store_data_task_inactive (s : State) (i : Inputs)
    (protocol : MemoryProtocol s i) (inactive : v9203 s i = 0) :
    TaskHolds ⟨5, by decide⟩ s i := by
  change decide (v9252 s i ≠ 1 ∨ v9250 s i = 1) = true
  simp [v9252, v9210, protocol.write_valid, inactive]

#print axioms store_data_task_of_equality
#print axioms store_data_task_inactive
end RiscvMiniProofs
