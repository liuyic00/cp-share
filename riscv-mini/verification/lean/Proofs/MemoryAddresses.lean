import Proofs.MemoryProtocol
namespace RiscvMiniProofs
open nCoreSoc

structure MemoryAddresses (s : State) (i : Inputs) : Prop where
  read : v9166 s i = 1 → s.g4.r154_ndut_5Fdpath_5Freq_5Faddr = v9171 s i
  write : v9203 s i = 1 → s.g4.r154_ndut_5Fdpath_5Freq_5Faddr = v9208 s i

def MemoryAddressTasks (s : State) (i : Inputs) : Prop :=
  TaskHolds ⟨1, by decide⟩ s i ∧ TaskHolds ⟨4, by decide⟩ s i

theorem memory_address_tasks (s : State) (i : Inputs)
    (protocol : MemoryProtocol s i) (addresses : MemoryAddresses s i) :
    MemoryAddressTasks s i := by
  constructor
  · change decide (v9175 s i ≠ 1 ∨ v9172 s i = 1) = true
    rcases BitVec.eq_zero_or_eq_one (v9166 s i) with idle | active
    · simp [v9175, v9173, protocol.read_valid, idle]
    · have address : v9169 s i = v9171 s i := addresses.read active
      simp [v9172, address]
  · change decide (v9212 s i ≠ 1 ∨ v9209 s i = 1) = true
    rcases BitVec.eq_zero_or_eq_one (v9203 s i) with idle | active
    · simp [v9212, v9210, protocol.write_valid, idle]
    · have address : v9206 s i = v9208 s i := addresses.write active
      simp [v9209, address]

theorem memory_addresses_idle (s : State) (i : Inputs) (idle : v964 s i = 0) :
    MemoryAddresses s i := by
  constructor
  · intro active
    simp [v9166, v9165, v9164, idle, v4] at active
  · intro active
    simp [v9203, v9202, v9201, idle, v4] at active

#print axioms memory_address_tasks
end RiscvMiniProofs
