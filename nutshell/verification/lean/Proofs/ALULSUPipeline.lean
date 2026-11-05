import Proofs.ALULSUUnits
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
def ALULSU (unit : BitVec 3) : Prop := unit = 0 ∨ unit = 1
def QueueALULSUTransport0 (s : State) : Prop :=
  ALULSU s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType
theorem queue_alulsu0_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueALULSUTransport0 (step s i) := by
  change ALULSU (v28448 s i)
  simp [ALULSU, v28448, reset, v4051, v2687]
theorem queue_alulsu0_step (s : State) (i : Inputs) (old : QueueALULSUTransport0 s) (source : v9827 s i = 1 → ALULSU (v28438 s i)) :
    QueueALULSUTransport0 (step s i) := by
  change ALULSU (v28448 s i)
  change ALULSU s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType at old
  have port1 := source
  have enq : v26198 s i = 1 → v9827 s i = 1 := fun h => (queue_enqueue_single s i h).1
  simp only [v28448, v2687, v28447, v28446, v28445, v28075, v28074, v28257, v28256, v28255, v28444, v28443, v28259, v28258, v28442, v28441, v28440, v28439, idu_two_instruction_enqueue_disabled]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [ALULSU, v2687, v26215, v26214, v26201, v26199, v26200, idu_second_port_disabled, v24]

def QueueALULSUTransport1 (s : State) : Prop :=
  ALULSU s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType
theorem queue_alulsu1_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueALULSUTransport1 (step s i) := by
  change ALULSU (v29657 s i)
  simp [ALULSU, v29657, reset, v4051, v2687]
theorem queue_alulsu1_step (s : State) (i : Inputs) (old : QueueALULSUTransport1 s) (source : v9827 s i = 1 → ALULSU (v28438 s i)) :
    QueueALULSUTransport1 (step s i) := by
  change ALULSU (v29657 s i)
  change ALULSU s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType at old
  have port1 := source
  have enq : v26198 s i = 1 → v9827 s i = 1 := fun h => (queue_enqueue_single s i h).1
  simp only [v29657, v2687, v29656, v29655, v29654, v29649, v29648, v28257, v28256, v28255, v29653, v29652, v29651, v29650, v28442, v28441, v28440, v28439, idu_two_instruction_enqueue_disabled]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [ALULSU, v2687, v26215, v26214, v26201, v26199, v26200, idu_second_port_disabled, v24]

def QueueALULSUTransport2 (s : State) : Prop :=
  ALULSU s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType
theorem queue_alulsu2_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueALULSUTransport2 (step s i) := by
  change ALULSU (v30123 s i)
  simp [ALULSU, v30123, reset, v4051, v2687]
theorem queue_alulsu2_step (s : State) (i : Inputs) (old : QueueALULSUTransport2 s) (source : v9827 s i = 1 → ALULSU (v28438 s i)) :
    QueueALULSUTransport2 (step s i) := by
  change ALULSU (v30123 s i)
  change ALULSU s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType at old
  have port1 := source
  have enq : v26198 s i = 1 → v9827 s i = 1 := fun h => (queue_enqueue_single s i h).1
  simp only [v30123, v2687, v30122, v30121, v30120, v30116, v9721, v28257, v28256, v28255, v30119, v30118, v30117, v28442, v28441, v28440, v28439, idu_two_instruction_enqueue_disabled]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [ALULSU, v2687, v26215, v26214, v26201, v26199, v26200, idu_second_port_disabled, v24]

def QueueALULSUTransport3 (s : State) : Prop :=
  ALULSU s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType
theorem queue_alulsu3_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueALULSUTransport3 (step s i) := by
  change ALULSU (v30563 s i)
  simp [ALULSU, v30563, reset, v4051, v2687]
theorem queue_alulsu3_step (s : State) (i : Inputs) (old : QueueALULSUTransport3 s) (source : v9827 s i = 1 → ALULSU (v28438 s i)) :
    QueueALULSUTransport3 (step s i) := by
  change ALULSU (v30563 s i)
  change ALULSU s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType at old
  have port1 := source
  have enq : v26198 s i = 1 → v9827 s i = 1 := fun h => (queue_enqueue_single s i h).1
  simp only [v30563, v2687, v30562, v30561, v30560, v30556, v2750, v28257, v28256, v28255, v30559, v30558, v30557, v28442, v28441, v28440, v28439, idu_two_instruction_enqueue_disabled]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [ALULSU, v2687, v26215, v26214, v26201, v26199, v26200, idu_second_port_disabled, v24]

def QueueALULSUTransportALULSUTransport (s : State) : Prop :=
  QueueALULSUTransport0 s ∧ QueueALULSUTransport1 s ∧ QueueALULSUTransport2 s ∧ QueueALULSUTransport3 s
theorem queue_selected_alulsu (s : State) (i : Inputs) (queue : QueueALULSUTransportALULSUTransport s) :
    ALULSU (v24912 s i) := by
  rcases queue with ⟨h0, h1, h2, h3⟩
  have bound := s.g59.r1900_nringBufferTail.isLt
  have cases : s.g59.r1900_nringBufferTail.toNat = 0 ∨ s.g59.r1900_nringBufferTail.toNat = 1 ∨ s.g59.r1900_nringBufferTail.toNat = 2 ∨ s.g59.r1900_nringBufferTail.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : s.g59.r1900_nringBufferTail = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, eq, QueueALULSUTransport0] using h0
  · have eq : s.g59.r1900_nringBufferTail = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, eq, QueueALULSUTransport1] using h1
  · have eq : s.g59.r1900_nringBufferTail = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, eq, QueueALULSUTransport2] using h2
  · have eq : s.g59.r1900_nringBufferTail = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, eq, QueueALULSUTransport3] using h3
def ExecuteALULSUTransportALULSUTransport (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 → ALULSU s.g48.r1553_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FfuType
theorem execute_alulsu_step (s : State) (i : Inputs)
    (queue : QueueALULSUTransportALULSUTransport s) (old : ExecuteALULSUTransportALULSUTransport s) :
    ExecuteALULSUTransportALULSUTransport (step s i) := by
  intro valid
  change ALULSU (v24913 s i)
  by_cases fire : v24283 s i = 1
  · simpa only [v24913, fire, ↓reduceIte] using queue_selected_alulsu s i queue
  · simp only [v24913, fire, ↓reduceIte]
    exact old (execute_valid_backward s i i valid fire)
def ALULSUTransportState (s : State) : Prop := QueueALULSUTransportALULSUTransport s ∧ ExecuteALULSUTransportALULSUTransport s
theorem alulsu_decode_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    ALULSUTransportState (step s i) := by
  constructor
  · exact ⟨queue_alulsu0_reset s i reset, queue_alulsu1_reset s i reset, queue_alulsu2_reset s i reset, queue_alulsu3_reset s i reset⟩
  · intro valid
    have zero := execute_valid_reset s i i reset
    change v6 (step s i) i = 1 at valid
    rw [zero] at valid
    contradiction
theorem alulsu_decode_step (s : State) (i : Inputs) (old : ALULSUTransportState s) (source : v9827 s i = 1 → ALULSU (v28438 s i)) :
    ALULSUTransportState (step s i) := by
  rcases old with ⟨queue, exu⟩
  refine ⟨?_, execute_alulsu_step s i queue exu⟩
  rcases queue with ⟨h0, h1, h2, h3⟩
  exact ⟨queue_alulsu0_step s i h0 source, queue_alulsu1_step s i h1 source, queue_alulsu2_step s i h2 source, queue_alulsu3_step s i h3 source⟩
theorem alulsu_decode_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (source : ∀ k, v9827 (run initial inputs (k + 1)) (inputs (k + 1)) = 1 → ALULSU (v28438 (run initial inputs (k + 1)) (inputs (k + 1)))) (t : Nat) :
    ALULSUTransportState (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact alulsu_decode_reset initial (inputs 0) reset
  | succ t ih => exact alulsu_decode_step _ _ ih (source t)
#print axioms alulsu_decode_run
end NutShellProofs
