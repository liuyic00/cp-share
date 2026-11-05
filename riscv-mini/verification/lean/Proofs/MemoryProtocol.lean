import Proofs.MemoryControl
import Proofs.PcBridge
namespace RiscvMiniProofs
open nCoreSoc

structure MemoryProtocol (s : State) (i : Inputs) : Prop where
  read_valid : v9156 s i = v9166 s i
  read_width : v9176 s i = v9190 s i
  write_valid : v9196 s i = v9203 s i
  write_width : v9253 s i = v9263 s i

def MemoryProtocolTasks (s : State) (i : Inputs) : Prop :=
  TaskHolds ⟨0, by decide⟩ s i ∧ TaskHolds ⟨2, by decide⟩ s i ∧
  TaskHolds ⟨3, by decide⟩ s i ∧ TaskHolds ⟨6, by decide⟩ s i

theorem memory_protocol_tasks (s : State) (i : Inputs) (protocol : MemoryProtocol s i) :
    MemoryProtocolTasks s i := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change decide (v9168 s i ≠ 1 ∨ v9167 s i = 1) = true
    simp [v9167, protocol.read_valid]
  · change decide (v9193 s i ≠ 1 ∨ v9191 s i = 1) = true
    simp [v9191, protocol.read_width]
  · change decide (v9205 s i ≠ 1 ∨ v9204 s i = 1) = true
    simp [v9204, protocol.write_valid]
  · change decide (v9266 s i ≠ 1 ∨ v9264 s i = 1) = true
    simp [v9264, protocol.write_width]

theorem memory_protocol_idle (s : State) (i : Inputs)
    (reset : i.nreset = 0) (control : MemoryControl s) (bubbles : BubbleAlignment s)
    (idle : v964 s i = 0) : MemoryProtocol s i := by
  have killed : s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 = 1 := by
    rcases BitVec.eq_zero_or_eq_one s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 with valid | killed
    · have commit := (commit_iff_valid_writeback s i reset).mpr valid
      rw [idle] at commit
      contradiction
    · exact killed
  have nop := bubbles.writeback killed
  have load := control.load
  have width := control.width
  have valid := control.valid
  rw [nop] at load width valid
  have nopLoad := addi_load (19 : BitVec 32) (by decide)
  have nopStore := addi_store (19 : BitVec 32) (by decide)
  rw [nopLoad] at load
  simp only [decode_store_valid, decode_store_width, nopStore, BitVec.reduceEq, ↓reduceIte] at width valid
  constructor
  · simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load, v200, v26, v29, v716, v22, v1941,
      v9166, v9165, v9164, idle, v4]
  · simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load, v200, v26, v29, v716, v22, v1941,
      v9190, v9189, v9188, idle]
  · simp [v9196, v9195, valid, v9203, v9202, v9201, idle, v4]
  · simp [v9253, width, v9263, v9262, v9261, idle, v1941]

#print axioms memory_protocol_tasks
#print axioms memory_protocol_idle
end RiscvMiniProofs
