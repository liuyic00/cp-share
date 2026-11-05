import Proofs.MemoryDispatch
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
def QueueDispatch0 (s : State) : Prop :=
  MemoryDispatch s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType
theorem queue_dispatch0_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueDispatch0 (step s i) := by
  change MemoryDispatch (v26233 s i) (v28448 s i)
  simp [MemoryDispatch, v26233, v28448, reset, v4051, v2687]
theorem queue_dispatch0_step (s : State) (i : Inputs) (old : QueueDispatch0 s) :
    QueueDispatch0 (step s i) := by
  change MemoryDispatch (v26233 s i) (v28448 s i)
  change MemoryDispatch s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType at old
  have port0 := idu_memory_dispatch_0 s i
  have port1 := idu_memory_dispatch_1 s i
  simp only [v26233, v4051, v26232, v26231, v26230, v26208, v26203, v26213, v26212, v26211, v26229, v26228, v26221, v26216, v26227, v26226, v26225, v26224, v28448, v2687, v28447, v28446, v28445, v28075, v28074, v28257, v28256, v28255, v28444, v28443, v28259, v28258, v28442, v28441, v28440, v28439]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [MemoryDispatch, v2687]

def QueueDispatch1 (s : State) : Prop :=
  MemoryDispatch s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType
theorem queue_dispatch1_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueDispatch1 (step s i) := by
  change MemoryDispatch (v29247 s i) (v29657 s i)
  simp [MemoryDispatch, v29247, v29657, reset, v4051, v2687]
theorem queue_dispatch1_step (s : State) (i : Inputs) (old : QueueDispatch1 s) :
    QueueDispatch1 (step s i) := by
  change MemoryDispatch (v29247 s i) (v29657 s i)
  change MemoryDispatch s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType at old
  have port0 := idu_memory_dispatch_0 s i
  have port1 := idu_memory_dispatch_1 s i
  simp only [v29247, v4051, v29246, v29245, v29244, v29239, v29238, v26213, v26212, v26211, v29243, v29242, v29241, v29240, v26227, v26226, v26225, v26224, v29657, v2687, v29656, v29655, v29654, v29649, v29648, v28257, v28256, v28255, v29653, v29652, v29651, v29650, v28442, v28441, v28440, v28439]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [MemoryDispatch, v2687]

def QueueDispatch2 (s : State) : Prop :=
  MemoryDispatch s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType
theorem queue_dispatch2_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueDispatch2 (step s i) := by
  change MemoryDispatch (v29795 s i) (v30123 s i)
  simp [MemoryDispatch, v29795, v30123, reset, v4051, v2687]
theorem queue_dispatch2_step (s : State) (i : Inputs) (old : QueueDispatch2 s) :
    QueueDispatch2 (step s i) := by
  change MemoryDispatch (v29795 s i) (v30123 s i)
  change MemoryDispatch s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType at old
  have port0 := idu_memory_dispatch_0 s i
  have port1 := idu_memory_dispatch_1 s i
  simp only [v29795, v4051, v29794, v29793, v29792, v29788, v9721, v26213, v26212, v26211, v29791, v29790, v29789, v26227, v26226, v26225, v26224, v30123, v2687, v30122, v30121, v30120, v30116, v28257, v28256, v28255, v30119, v30118, v30117, v28442, v28441, v28440, v28439]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [MemoryDispatch, v2687]

def QueueDispatch3 (s : State) : Prop :=
  MemoryDispatch s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType
theorem queue_dispatch3_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueDispatch3 (step s i) := by
  change MemoryDispatch (v30235 s i) (v30563 s i)
  simp [MemoryDispatch, v30235, v30563, reset, v4051, v2687]
theorem queue_dispatch3_step (s : State) (i : Inputs) (old : QueueDispatch3 s) :
    QueueDispatch3 (step s i) := by
  change MemoryDispatch (v30235 s i) (v30563 s i)
  change MemoryDispatch s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType at old
  have port0 := idu_memory_dispatch_0 s i
  have port1 := idu_memory_dispatch_1 s i
  simp only [v30235, v4051, v30234, v30233, v30232, v30228, v2750, v26213, v26212, v26211, v30231, v30230, v30229, v26227, v26226, v26225, v26224, v30563, v2687, v30562, v30561, v30560, v30556, v28257, v28256, v28255, v30559, v30558, v30557, v28442, v28441, v28440, v28439]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [MemoryDispatch, v2687]

def QueueDispatchDispatch (s : State) : Prop :=
  QueueDispatch0 s ∧ QueueDispatch1 s ∧ QueueDispatch2 s ∧ QueueDispatch3 s
theorem queue_selected_dispatch (s : State) (i : Inputs) (queue : QueueDispatchDispatch s) :
    MemoryDispatch (v24297 s i) (v24912 s i) := by
  rcases queue with ⟨h0, h1, h2, h3⟩
  have bound := s.g59.r1900_nringBufferTail.isLt
  have cases : s.g59.r1900_nringBufferTail.toNat = 0 ∨ s.g59.r1900_nringBufferTail.toNat = 1 ∨ s.g59.r1900_nringBufferTail.toNat = 2 ∨ s.g59.r1900_nringBufferTail.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : s.g59.r1900_nringBufferTail = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, eq, QueueDispatch0] using h0
  · have eq : s.g59.r1900_nringBufferTail = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, eq, QueueDispatch1] using h1
  · have eq : s.g59.r1900_nringBufferTail = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, eq, QueueDispatch2] using h2
  · have eq : s.g59.r1900_nringBufferTail = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, eq, QueueDispatch3] using h3
def ExecuteDispatchDispatch (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 → MemoryDispatch s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr s.g48.r1553_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FfuType
theorem execute_dispatch_step (s : State) (i : Inputs)
    (queue : QueueDispatchDispatch s) (old : ExecuteDispatchDispatch s) :
    ExecuteDispatchDispatch (step s i) := by
  intro valid
  change MemoryDispatch (v24298 s i) (v24913 s i)
  by_cases fire : v24283 s i = 1
  · simpa only [v24298, v24913, fire, ↓reduceIte] using queue_selected_dispatch s i queue
  · simp only [v24298, v24913, fire, ↓reduceIte]
    exact old (execute_valid_backward s i i valid fire)
def DispatchState (s : State) : Prop := QueueDispatchDispatch s ∧ ExecuteDispatchDispatch s
theorem dispatch_decode_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    DispatchState (step s i) := by
  constructor
  · exact ⟨queue_dispatch0_reset s i reset, queue_dispatch1_reset s i reset, queue_dispatch2_reset s i reset, queue_dispatch3_reset s i reset⟩
  · intro valid
    have zero := execute_valid_reset s i i reset
    change v6 (step s i) i = 1 at valid
    rw [zero] at valid
    contradiction
theorem dispatch_decode_step (s : State) (i : Inputs) (old : DispatchState s) :
    DispatchState (step s i) := by
  rcases old with ⟨queue, exu⟩
  refine ⟨?_, execute_dispatch_step s i queue exu⟩
  rcases queue with ⟨h0, h1, h2, h3⟩
  exact ⟨queue_dispatch0_step s i h0, queue_dispatch1_step s i h1, queue_dispatch2_step s i h2, queue_dispatch3_step s i h3⟩
theorem dispatch_decode_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    DispatchState (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact dispatch_decode_reset initial (inputs 0) reset
  | succ t ih => exact dispatch_decode_step _ _ ih
#print axioms dispatch_decode_run
end NutShellProofs
