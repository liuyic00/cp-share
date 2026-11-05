import Proofs.BranchPipeline
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def AluPageFaultsClear (unit : BitVec 3) (b0 : BitVec 1) : Prop :=
  unit = 0 → b0 = 0
theorem idu_alu_page_faults_0 (s : State) (i : Inputs) :
    AluPageFaultsClear (v28254 s i) (v26382 s i) := by
  intro alu
  have inactive : v28077 s i ≠ 1 := by
    intro active; simp [v28254, active, v28078] at alu
  rcases BitVec.eq_zero_or_eq_one (v26382 s i) with zero | one
  · exact zero
  · rcases BitVec.eq_zero_or_eq_one (v26380 s i) with a | a <;> rcases BitVec.eq_zero_or_eq_one (v26360 s i) with b | b <;> simp [v28077, v28076, one, a, b] at inactive
theorem idu_alu_page_faults_1 (s : State) (i : Inputs) :
    AluPageFaultsClear (v28438 s i) (v26909 s i) := by
  intro alu
  have inactive : v28261 s i ≠ 1 := by
    intro active; simp [v28438, active, v28262] at alu
  rcases BitVec.eq_zero_or_eq_one (v26909 s i) with zero | one
  · exact zero
  · rcases BitVec.eq_zero_or_eq_one (v10039 s i) with a | a <;> rcases BitVec.eq_zero_or_eq_one (v26367 s i) with b | b <;> simp [v28261, v28260, one, a, b] at inactive
def QueueAluPageFaults0 (s : State) : Prop := AluPageFaultsClear s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType s.g53.r1697_ndataBuffer_5F0_5Fcf_5FexceptionVec_5F12
theorem queue_alu_page_faults0_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueAluPageFaults0 (step s i) := by
  change AluPageFaultsClear (v28448 s i) (v27609 s i)
  simp [v28448, v27609, reset, AluPageFaultsClear, v24]
theorem queue_alu_page_faults0_step (s : State) (i : Inputs) (old : QueueAluPageFaults0 s) :
    QueueAluPageFaults0 (step s i) := by
  change AluPageFaultsClear (v28448 s i) (v27609 s i)
  change AluPageFaultsClear s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType s.g53.r1697_ndataBuffer_5F0_5Fcf_5FexceptionVec_5F12 at old
  have port0 := idu_alu_page_faults_0 s i
  have port1 := idu_alu_page_faults_1 s i
  simp only [v28448, v2687, v28447, v28446, v28445, v28075, v28074, v28257, v28256, v28255, v28444, v28443, v28259, v28258, v28442, v28441, v28440, v28439, v27609, v24, v27608, v27607, v27606, v27594, v27593, v27597, v27596, v27595, v27605, v27604, v27599, v27598, v27603, v27602, v27601, v27600]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [AluPageFaultsClear]
def QueueAluPageFaults1 (s : State) : Prop := AluPageFaultsClear s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType s.g54.r1752_ndataBuffer_5F1_5Fcf_5FexceptionVec_5F12
theorem queue_alu_page_faults1_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueAluPageFaults1 (step s i) := by
  change AluPageFaultsClear (v29657 s i) (v29427 s i)
  simp [v29657, v29427, reset, AluPageFaultsClear, v24]
theorem queue_alu_page_faults1_step (s : State) (i : Inputs) (old : QueueAluPageFaults1 s) :
    QueueAluPageFaults1 (step s i) := by
  change AluPageFaultsClear (v29657 s i) (v29427 s i)
  change AluPageFaultsClear s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType s.g54.r1752_ndataBuffer_5F1_5Fcf_5FexceptionVec_5F12 at old
  have port0 := idu_alu_page_faults_0 s i
  have port1 := idu_alu_page_faults_1 s i
  simp only [v29657, v2687, v29656, v29655, v29654, v29649, v29648, v28257, v28256, v28255, v29653, v29652, v29651, v29650, v28442, v28441, v28440, v28439, v29427, v24, v29426, v29425, v29424, v29419, v29418, v27597, v27596, v27595, v29423, v29422, v29421, v29420, v27603, v27602, v27601, v27600]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [AluPageFaultsClear]
def QueueAluPageFaults2 (s : State) : Prop := AluPageFaultsClear s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType s.g56.r1807_ndataBuffer_5F2_5Fcf_5FexceptionVec_5F12
theorem queue_alu_page_faults2_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueAluPageFaults2 (step s i) := by
  change AluPageFaultsClear (v30123 s i) (v29939 s i)
  simp [v30123, v29939, reset, AluPageFaultsClear, v24]
theorem queue_alu_page_faults2_step (s : State) (i : Inputs) (old : QueueAluPageFaults2 s) :
    QueueAluPageFaults2 (step s i) := by
  change AluPageFaultsClear (v30123 s i) (v29939 s i)
  change AluPageFaultsClear s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType s.g56.r1807_ndataBuffer_5F2_5Fcf_5FexceptionVec_5F12 at old
  have port0 := idu_alu_page_faults_0 s i
  have port1 := idu_alu_page_faults_1 s i
  simp only [v30123, v2687, v30122, v30121, v30120, v30116, v9721, v28257, v28256, v28255, v30119, v30118, v30117, v28442, v28441, v28440, v28439, v29939, v24, v29938, v29937, v29936, v29932, v27597, v27596, v27595, v29935, v29934, v29933, v27603, v27602, v27601, v27600]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [AluPageFaultsClear]
def QueueAluPageFaults3 (s : State) : Prop := AluPageFaultsClear s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType s.g58.r1862_ndataBuffer_5F3_5Fcf_5FexceptionVec_5F12
theorem queue_alu_page_faults3_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueAluPageFaults3 (step s i) := by
  change AluPageFaultsClear (v30563 s i) (v30379 s i)
  simp [v30563, v30379, reset, AluPageFaultsClear, v24]
theorem queue_alu_page_faults3_step (s : State) (i : Inputs) (old : QueueAluPageFaults3 s) :
    QueueAluPageFaults3 (step s i) := by
  change AluPageFaultsClear (v30563 s i) (v30379 s i)
  change AluPageFaultsClear s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType s.g58.r1862_ndataBuffer_5F3_5Fcf_5FexceptionVec_5F12 at old
  have port0 := idu_alu_page_faults_0 s i
  have port1 := idu_alu_page_faults_1 s i
  simp only [v30563, v2687, v30562, v30561, v30560, v30556, v2750, v28257, v28256, v28255, v30559, v30558, v30557, v28442, v28441, v28440, v28439, v30379, v24, v30378, v30377, v30376, v30372, v27597, v27596, v27595, v30375, v30374, v30373, v27603, v27602, v27601, v27600]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [AluPageFaultsClear]
def QueueAluPageFaults (s : State) : Prop := QueueAluPageFaults0 s ∧ QueueAluPageFaults1 s ∧ QueueAluPageFaults2 s ∧ QueueAluPageFaults3 s
theorem queue_selected_alu_page_faults (s : State) (i : Inputs) (queue : QueueAluPageFaults s) :
    AluPageFaultsClear (v24912 s i) (v24567 s i) := by
  rcases queue with ⟨h0, h1, h2, h3⟩
  have bound := s.g59.r1900_nringBufferTail.isLt
  have cases : s.g59.r1900_nringBufferTail.toNat = 0 ∨ s.g59.r1900_nringBufferTail.toNat = 1 ∨ s.g59.r1900_nringBufferTail.toNat = 2 ∨ s.g59.r1900_nringBufferTail.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : s.g59.r1900_nringBufferTail = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, v24567, v24566, v24565, v24564, v24554, v24563, v24555, v24562, v24557, v24556, v24561, v24560, v24559, v24558, eq, QueueAluPageFaults0] using h0
  · have eq : s.g59.r1900_nringBufferTail = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, v24567, v24566, v24565, v24564, v24554, v24563, v24555, v24562, v24557, v24556, v24561, v24560, v24559, v24558, eq, QueueAluPageFaults1] using h1
  · have eq : s.g59.r1900_nringBufferTail = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, v24567, v24566, v24565, v24564, v24554, v24563, v24555, v24562, v24557, v24556, v24561, v24560, v24559, v24558, eq, QueueAluPageFaults2] using h2
  · have eq : s.g59.r1900_nringBufferTail = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, v24567, v24566, v24565, v24564, v24554, v24563, v24555, v24562, v24557, v24556, v24561, v24560, v24559, v24558, eq, QueueAluPageFaults3] using h3
def ExecuteAluPageFaults (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 → AluPageFaultsClear s.g48.r1553_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FfuType s.g47.r1530_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F12
theorem execute_alu_page_faults_step (s : State) (i : Inputs)
    (queue : QueueAluPageFaults s) (old : ExecuteAluPageFaults s) :
    ExecuteAluPageFaults (step s i) := by
  intro valid
  change AluPageFaultsClear (v24913 s i) (v24568 s i)
  by_cases fire : v24283 s i = 1
  · simpa only [v24913, v24568, fire, ↓reduceIte] using queue_selected_alu_page_faults s i queue
  · simp only [v24913, v24568, fire, ↓reduceIte]
    exact old (execute_valid_backward s i i valid fire)
def AluPageFaultState (s : State) : Prop := QueueAluPageFaults s ∧ ExecuteAluPageFaults s
theorem alu_page_fault_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    AluPageFaultState (step s i) := by
  constructor
  · exact ⟨queue_alu_page_faults0_reset s i reset, queue_alu_page_faults1_reset s i reset, queue_alu_page_faults2_reset s i reset, queue_alu_page_faults3_reset s i reset⟩
  · intro valid
    have zero := execute_valid_reset s i i reset
    change v6 (step s i) i = 1 at valid
    rw [zero] at valid
    contradiction
theorem alu_page_fault_step (s : State) (i : Inputs) (old : AluPageFaultState s) :
    AluPageFaultState (step s i) := by
  rcases old with ⟨queue, exu⟩
  refine ⟨?_, execute_alu_page_faults_step s i queue exu⟩
  rcases queue with ⟨h0, h1, h2, h3⟩
  exact ⟨queue_alu_page_faults0_step s i h0, queue_alu_page_faults1_step s i h1, queue_alu_page_faults2_step s i h2, queue_alu_page_faults3_step s i h3⟩
theorem alu_page_fault_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    AluPageFaultState (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact alu_page_fault_reset initial (inputs 0) reset
  | succ t ih => exact alu_page_fault_step _ _ ih
#print axioms alu_page_fault_run
end NutShellProofs
