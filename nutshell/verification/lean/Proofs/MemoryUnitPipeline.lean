import Proofs.MemoryUnit
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
def QueueMemoryUnitTransport0 (s : State) : Prop :=
  MemoryUnit s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType
theorem queue_memory_unit0_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueMemoryUnitTransport0 (step s i) := by
  change MemoryUnit (v26233 s i) (v28448 s i)
  simp only [MemoryUnit, v26233, v28448, reset, v4051, v2687, ↓reduceIte]
  intro operation; cases operation <;> simp [IsMemory, MemoryOp.encoding]
theorem queue_memory_unit0_step (s : State) (i : Inputs) (old : QueueMemoryUnitTransport0 s) :
    QueueMemoryUnitTransport0 (step s i) := by
  change MemoryUnit (v26233 s i) (v28448 s i)
  change MemoryUnit s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType at old
  have port0 := idu_memory_unit_0 s i
  have port1 := idu_memory_unit_1 s i
  simp only [v26233, v4051, v26232, v26231, v26230, v26208, v26203, v26213, v26212, v26211, v26229, v26228, v26221, v26216, v26227, v26226, v26225, v26224, v28448, v2687, v28447, v28446, v28445, v28075, v28074, v28257, v28256, v28255, v28444, v28443, v28259, v28258, v28442, v28441, v28440, v28439]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [MemoryUnit, v2687]
  all_goals intro operation; cases operation <;> simp [IsMemory, MemoryOp.encoding]

def QueueMemoryUnitTransport1 (s : State) : Prop :=
  MemoryUnit s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType
theorem queue_memory_unit1_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueMemoryUnitTransport1 (step s i) := by
  change MemoryUnit (v29247 s i) (v29657 s i)
  simp only [MemoryUnit, v29247, v29657, reset, v4051, v2687, ↓reduceIte]
  intro operation; cases operation <;> simp [IsMemory, MemoryOp.encoding]
theorem queue_memory_unit1_step (s : State) (i : Inputs) (old : QueueMemoryUnitTransport1 s) :
    QueueMemoryUnitTransport1 (step s i) := by
  change MemoryUnit (v29247 s i) (v29657 s i)
  change MemoryUnit s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType at old
  have port0 := idu_memory_unit_0 s i
  have port1 := idu_memory_unit_1 s i
  simp only [v29247, v4051, v29246, v29245, v29244, v29239, v29238, v26213, v26212, v26211, v29243, v29242, v29241, v29240, v26227, v26226, v26225, v26224, v29657, v2687, v29656, v29655, v29654, v29649, v29648, v28257, v28256, v28255, v29653, v29652, v29651, v29650, v28442, v28441, v28440, v28439]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [MemoryUnit, v2687]
  all_goals intro operation; cases operation <;> simp [IsMemory, MemoryOp.encoding]

def QueueMemoryUnitTransport2 (s : State) : Prop :=
  MemoryUnit s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType
theorem queue_memory_unit2_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueMemoryUnitTransport2 (step s i) := by
  change MemoryUnit (v29795 s i) (v30123 s i)
  simp only [MemoryUnit, v29795, v30123, reset, v4051, v2687, ↓reduceIte]
  intro operation; cases operation <;> simp [IsMemory, MemoryOp.encoding]
theorem queue_memory_unit2_step (s : State) (i : Inputs) (old : QueueMemoryUnitTransport2 s) :
    QueueMemoryUnitTransport2 (step s i) := by
  change MemoryUnit (v29795 s i) (v30123 s i)
  change MemoryUnit s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType at old
  have port0 := idu_memory_unit_0 s i
  have port1 := idu_memory_unit_1 s i
  simp only [v29795, v4051, v29794, v29793, v29792, v29788, v9721, v26213, v26212, v26211, v29791, v29790, v29789, v26227, v26226, v26225, v26224, v30123, v2687, v30122, v30121, v30120, v30116, v28257, v28256, v28255, v30119, v30118, v30117, v28442, v28441, v28440, v28439]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [MemoryUnit, v2687]
  all_goals intro operation; cases operation <;> simp [IsMemory, MemoryOp.encoding]

def QueueMemoryUnitTransport3 (s : State) : Prop :=
  MemoryUnit s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType
theorem queue_memory_unit3_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueMemoryUnitTransport3 (step s i) := by
  change MemoryUnit (v30235 s i) (v30563 s i)
  simp only [MemoryUnit, v30235, v30563, reset, v4051, v2687, ↓reduceIte]
  intro operation; cases operation <;> simp [IsMemory, MemoryOp.encoding]
theorem queue_memory_unit3_step (s : State) (i : Inputs) (old : QueueMemoryUnitTransport3 s) :
    QueueMemoryUnitTransport3 (step s i) := by
  change MemoryUnit (v30235 s i) (v30563 s i)
  change MemoryUnit s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType at old
  have port0 := idu_memory_unit_0 s i
  have port1 := idu_memory_unit_1 s i
  simp only [v30235, v4051, v30234, v30233, v30232, v30228, v2750, v26213, v26212, v26211, v30231, v30230, v30229, v26227, v26226, v26225, v26224, v30563, v2687, v30562, v30561, v30560, v30556, v28257, v28256, v28255, v30559, v30558, v30557, v28442, v28441, v28440, v28439]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [MemoryUnit, v2687]
  all_goals intro operation; cases operation <;> simp [IsMemory, MemoryOp.encoding]

def QueueMemoryUnitTransportMemoryUnitTransport (s : State) : Prop :=
  QueueMemoryUnitTransport0 s ∧ QueueMemoryUnitTransport1 s ∧ QueueMemoryUnitTransport2 s ∧ QueueMemoryUnitTransport3 s
theorem queue_selected_memory_unit (s : State) (i : Inputs) (queue : QueueMemoryUnitTransportMemoryUnitTransport s) :
    MemoryUnit (v24297 s i) (v24912 s i) := by
  rcases queue with ⟨h0, h1, h2, h3⟩
  have bound := s.g59.r1900_nringBufferTail.isLt
  have cases : s.g59.r1900_nringBufferTail.toNat = 0 ∨ s.g59.r1900_nringBufferTail.toNat = 1 ∨ s.g59.r1900_nringBufferTail.toNat = 2 ∨ s.g59.r1900_nringBufferTail.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : s.g59.r1900_nringBufferTail = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, eq, QueueMemoryUnitTransport0] using h0
  · have eq : s.g59.r1900_nringBufferTail = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, eq, QueueMemoryUnitTransport1] using h1
  · have eq : s.g59.r1900_nringBufferTail = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, eq, QueueMemoryUnitTransport2] using h2
  · have eq : s.g59.r1900_nringBufferTail = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, eq, QueueMemoryUnitTransport3] using h3
def ExecuteMemoryUnitTransportMemoryUnitTransport (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 → MemoryUnit s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr s.g48.r1553_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FfuType
theorem execute_memory_unit_step (s : State) (i : Inputs)
    (queue : QueueMemoryUnitTransportMemoryUnitTransport s) (old : ExecuteMemoryUnitTransportMemoryUnitTransport s) :
    ExecuteMemoryUnitTransportMemoryUnitTransport (step s i) := by
  intro valid
  change MemoryUnit (v24298 s i) (v24913 s i)
  by_cases fire : v24283 s i = 1
  · simpa only [v24298, v24913, fire, ↓reduceIte] using queue_selected_memory_unit s i queue
  · simp only [v24298, v24913, fire, ↓reduceIte]
    exact old (execute_valid_backward s i i valid fire)
def MemoryUnitTransportState (s : State) : Prop := QueueMemoryUnitTransportMemoryUnitTransport s ∧ ExecuteMemoryUnitTransportMemoryUnitTransport s
theorem memory_unit_decode_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    MemoryUnitTransportState (step s i) := by
  constructor
  · exact ⟨queue_memory_unit0_reset s i reset, queue_memory_unit1_reset s i reset, queue_memory_unit2_reset s i reset, queue_memory_unit3_reset s i reset⟩
  · intro valid
    have zero := execute_valid_reset s i i reset
    change v6 (step s i) i = 1 at valid
    rw [zero] at valid
    contradiction
theorem memory_unit_decode_step (s : State) (i : Inputs) (old : MemoryUnitTransportState s) :
    MemoryUnitTransportState (step s i) := by
  rcases old with ⟨queue, exu⟩
  refine ⟨?_, execute_memory_unit_step s i queue exu⟩
  rcases queue with ⟨h0, h1, h2, h3⟩
  exact ⟨queue_memory_unit0_step s i h0, queue_memory_unit1_step s i h1, queue_memory_unit2_step s i h2, queue_memory_unit3_step s i h3⟩
theorem memory_unit_decode_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    MemoryUnitTransportState (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact memory_unit_decode_reset initial (inputs 0) reset
  | succ t ih => exact memory_unit_decode_step _ _ ih
#print axioms memory_unit_decode_run
end NutShellProofs
