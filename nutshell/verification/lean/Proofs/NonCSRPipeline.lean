import Proofs.TemporaryPC32
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
def NonCSR (unit : BitVec 3) : Prop := unit ≠ 3
def QueueNonCSRTransport0 (s : State) : Prop :=
  NonCSR s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType
theorem queue_noncsr0_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueNonCSRTransport0 (step s i) := by
  change NonCSR (v28448 s i)
  simp [NonCSR, v28448, reset, v4051, v2687]
theorem queue_noncsr0_step (s : State) (i : Inputs) (old : QueueNonCSRTransport0 s) (source : v9827 s i = 1 → v28438 s i ≠ 3) :
    QueueNonCSRTransport0 (step s i) := by
  change NonCSR (v28448 s i)
  change NonCSR s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType at old
  have port1 := source
  have enq : v26198 s i = 1 → v9827 s i = 1 := fun h => (queue_enqueue_single s i h).1
  simp only [v28448, v2687, v28447, v28446, v28445, v28075, v28074, v28257, v28256, v28255, v28444, v28443, v28259, v28258, v28442, v28441, v28440, v28439, idu_two_instruction_enqueue_disabled]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [NonCSR, v2687, v26215, v26214, v26201, v26199, v26200, idu_second_port_disabled, v24]

def QueueNonCSRTransport1 (s : State) : Prop :=
  NonCSR s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType
theorem queue_noncsr1_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueNonCSRTransport1 (step s i) := by
  change NonCSR (v29657 s i)
  simp [NonCSR, v29657, reset, v4051, v2687]
theorem queue_noncsr1_step (s : State) (i : Inputs) (old : QueueNonCSRTransport1 s) (source : v9827 s i = 1 → v28438 s i ≠ 3) :
    QueueNonCSRTransport1 (step s i) := by
  change NonCSR (v29657 s i)
  change NonCSR s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType at old
  have port1 := source
  have enq : v26198 s i = 1 → v9827 s i = 1 := fun h => (queue_enqueue_single s i h).1
  simp only [v29657, v2687, v29656, v29655, v29654, v29649, v29648, v28257, v28256, v28255, v29653, v29652, v29651, v29650, v28442, v28441, v28440, v28439, idu_two_instruction_enqueue_disabled]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [NonCSR, v2687, v26215, v26214, v26201, v26199, v26200, idu_second_port_disabled, v24]

def QueueNonCSRTransport2 (s : State) : Prop :=
  NonCSR s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType
theorem queue_noncsr2_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueNonCSRTransport2 (step s i) := by
  change NonCSR (v30123 s i)
  simp [NonCSR, v30123, reset, v4051, v2687]
theorem queue_noncsr2_step (s : State) (i : Inputs) (old : QueueNonCSRTransport2 s) (source : v9827 s i = 1 → v28438 s i ≠ 3) :
    QueueNonCSRTransport2 (step s i) := by
  change NonCSR (v30123 s i)
  change NonCSR s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType at old
  have port1 := source
  have enq : v26198 s i = 1 → v9827 s i = 1 := fun h => (queue_enqueue_single s i h).1
  simp only [v30123, v2687, v30122, v30121, v30120, v30116, v9721, v28257, v28256, v28255, v30119, v30118, v30117, v28442, v28441, v28440, v28439, idu_two_instruction_enqueue_disabled]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [NonCSR, v2687, v26215, v26214, v26201, v26199, v26200, idu_second_port_disabled, v24]

def QueueNonCSRTransport3 (s : State) : Prop :=
  NonCSR s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType
theorem queue_noncsr3_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueNonCSRTransport3 (step s i) := by
  change NonCSR (v30563 s i)
  simp [NonCSR, v30563, reset, v4051, v2687]
theorem queue_noncsr3_step (s : State) (i : Inputs) (old : QueueNonCSRTransport3 s) (source : v9827 s i = 1 → v28438 s i ≠ 3) :
    QueueNonCSRTransport3 (step s i) := by
  change NonCSR (v30563 s i)
  change NonCSR s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType at old
  have port1 := source
  have enq : v26198 s i = 1 → v9827 s i = 1 := fun h => (queue_enqueue_single s i h).1
  simp only [v30563, v2687, v30562, v30561, v30560, v30556, v2750, v28257, v28256, v28255, v30559, v30558, v30557, v28442, v28441, v28440, v28439, idu_two_instruction_enqueue_disabled]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [NonCSR, v2687, v26215, v26214, v26201, v26199, v26200, idu_second_port_disabled, v24]

def QueueNonCSRTransportNonCSRTransport (s : State) : Prop :=
  QueueNonCSRTransport0 s ∧ QueueNonCSRTransport1 s ∧ QueueNonCSRTransport2 s ∧ QueueNonCSRTransport3 s
theorem queue_selected_noncsr (s : State) (i : Inputs) (queue : QueueNonCSRTransportNonCSRTransport s) :
    NonCSR (v24912 s i) := by
  rcases queue with ⟨h0, h1, h2, h3⟩
  have bound := s.g59.r1900_nringBufferTail.isLt
  have cases : s.g59.r1900_nringBufferTail.toNat = 0 ∨ s.g59.r1900_nringBufferTail.toNat = 1 ∨ s.g59.r1900_nringBufferTail.toNat = 2 ∨ s.g59.r1900_nringBufferTail.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : s.g59.r1900_nringBufferTail = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, eq, QueueNonCSRTransport0] using h0
  · have eq : s.g59.r1900_nringBufferTail = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, eq, QueueNonCSRTransport1] using h1
  · have eq : s.g59.r1900_nringBufferTail = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, eq, QueueNonCSRTransport2] using h2
  · have eq : s.g59.r1900_nringBufferTail = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, eq, QueueNonCSRTransport3] using h3
def ExecuteNonCSRTransportNonCSRTransport (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 → NonCSR s.g48.r1553_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FfuType
theorem execute_noncsr_step (s : State) (i : Inputs)
    (queue : QueueNonCSRTransportNonCSRTransport s) (old : ExecuteNonCSRTransportNonCSRTransport s) :
    ExecuteNonCSRTransportNonCSRTransport (step s i) := by
  intro valid
  change NonCSR (v24913 s i)
  by_cases fire : v24283 s i = 1
  · simpa only [v24913, fire, ↓reduceIte] using queue_selected_noncsr s i queue
  · simp only [v24913, fire, ↓reduceIte]
    exact old (execute_valid_backward s i i valid fire)
def NonCSRTransportState (s : State) : Prop := QueueNonCSRTransportNonCSRTransport s ∧ ExecuteNonCSRTransportNonCSRTransport s
theorem noncsr_decode_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    NonCSRTransportState (step s i) := by
  constructor
  · exact ⟨queue_noncsr0_reset s i reset, queue_noncsr1_reset s i reset, queue_noncsr2_reset s i reset, queue_noncsr3_reset s i reset⟩
  · intro valid
    have zero := execute_valid_reset s i i reset
    change v6 (step s i) i = 1 at valid
    rw [zero] at valid
    contradiction
theorem noncsr_decode_step (s : State) (i : Inputs) (old : NonCSRTransportState s) (source : v9827 s i = 1 → v28438 s i ≠ 3) :
    NonCSRTransportState (step s i) := by
  rcases old with ⟨queue, exu⟩
  refine ⟨?_, execute_noncsr_step s i queue exu⟩
  rcases queue with ⟨h0, h1, h2, h3⟩
  exact ⟨queue_noncsr0_step s i h0 source, queue_noncsr1_step s i h1 source, queue_noncsr2_step s i h2 source, queue_noncsr3_step s i h3 source⟩
theorem noncsr_decode_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (source : ∀ k, v9827 (run initial inputs (k + 1)) (inputs (k + 1)) = 1 → v28438 (run initial inputs (k + 1)) (inputs (k + 1)) ≠ 3) (t : Nat) :
    NonCSRTransportState (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact noncsr_decode_reset initial (inputs 0) reset
  | succ t ih => exact noncsr_decode_step _ _ ih (source t)
#print axioms noncsr_decode_run
end NutShellProofs
