import Proofs.BranchPipeline
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def AluAccessFaultsClear (unit : BitVec 3) (b0 : BitVec 1) : Prop :=
  unit = 0 → b0 = 0
theorem idu_alu_access_faults_0 (s : State) (i : Inputs) :
    AluAccessFaultsClear (v28254 s i) (v26360 s i) := by
  intro alu
  have inactive : v28077 s i ≠ 1 := by
    intro active; simp [v28254, active, v28078] at alu
  rcases BitVec.eq_zero_or_eq_one (v26360 s i) with zero | one
  · exact zero
  · rcases BitVec.eq_zero_or_eq_one (v26380 s i) with a | a <;> rcases BitVec.eq_zero_or_eq_one (v26382 s i) with b | b <;> simp [v28077, v28076, one, a, b] at inactive
theorem idu_alu_access_faults_1 (s : State) (i : Inputs) :
    AluAccessFaultsClear (v28438 s i) (v26367 s i) := by
  intro alu
  have inactive : v28261 s i ≠ 1 := by
    intro active; simp [v28438, active, v28262] at alu
  rcases BitVec.eq_zero_or_eq_one (v26367 s i) with zero | one
  · exact zero
  · rcases BitVec.eq_zero_or_eq_one (v10039 s i) with a | a <;> rcases BitVec.eq_zero_or_eq_one (v26909 s i) with b | b <;> simp [v28261, v28260, one, a, b] at inactive
def QueueAluAccessFaults0 (s : State) : Prop := AluAccessFaultsClear s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType s.g52.r1686_ndataBuffer_5F0_5Fcf_5FexceptionVec_5F1
theorem queue_alu_access_faults0_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueAluAccessFaults0 (step s i) := by
  change AluAccessFaultsClear (v28448 s i) (v26376 s i)
  simp [v28448, v26376, reset, AluAccessFaultsClear, v24]
theorem queue_alu_access_faults0_step (s : State) (i : Inputs) (old : QueueAluAccessFaults0 s) :
    QueueAluAccessFaults0 (step s i) := by
  change AluAccessFaultsClear (v28448 s i) (v26376 s i)
  change AluAccessFaultsClear s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType s.g52.r1686_ndataBuffer_5F0_5Fcf_5FexceptionVec_5F1 at old
  have port0 := idu_alu_access_faults_0 s i
  have port1 := idu_alu_access_faults_1 s i
  simp only [v28448, v2687, v28447, v28446, v28445, v28075, v28074, v28257, v28256, v28255, v28444, v28443, v28259, v28258, v28442, v28441, v28440, v28439, v26376, v24, v26375, v26374, v26373, v26357, v26356, v26362, v26361, v26372, v26371, v26364, v26363, v26370, v26369, v26368]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [AluAccessFaultsClear]
def QueueAluAccessFaults1 (s : State) : Prop := AluAccessFaultsClear s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType s.g54.r1741_ndataBuffer_5F1_5Fcf_5FexceptionVec_5F1
theorem queue_alu_access_faults1_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueAluAccessFaults1 (step s i) := by
  change AluAccessFaultsClear (v29657 s i) (v29317 s i)
  simp [v29657, v29317, reset, AluAccessFaultsClear, v24]
theorem queue_alu_access_faults1_step (s : State) (i : Inputs) (old : QueueAluAccessFaults1 s) :
    QueueAluAccessFaults1 (step s i) := by
  change AluAccessFaultsClear (v29657 s i) (v29317 s i)
  change AluAccessFaultsClear s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType s.g54.r1741_ndataBuffer_5F1_5Fcf_5FexceptionVec_5F1 at old
  have port0 := idu_alu_access_faults_0 s i
  have port1 := idu_alu_access_faults_1 s i
  simp only [v29657, v2687, v29656, v29655, v29654, v29649, v29648, v28257, v28256, v28255, v29653, v29652, v29651, v29650, v28442, v28441, v28440, v28439, v29317, v24, v29316, v29315, v29314, v29309, v29308, v26362, v26361, v29313, v29312, v29311, v29310, v26370, v26369, v26368]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [AluAccessFaultsClear]
def QueueAluAccessFaults2 (s : State) : Prop := AluAccessFaultsClear s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType s.g56.r1796_ndataBuffer_5F2_5Fcf_5FexceptionVec_5F1
theorem queue_alu_access_faults2_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueAluAccessFaults2 (step s i) := by
  change AluAccessFaultsClear (v30123 s i) (v29851 s i)
  simp [v30123, v29851, reset, AluAccessFaultsClear, v24]
theorem queue_alu_access_faults2_step (s : State) (i : Inputs) (old : QueueAluAccessFaults2 s) :
    QueueAluAccessFaults2 (step s i) := by
  change AluAccessFaultsClear (v30123 s i) (v29851 s i)
  change AluAccessFaultsClear s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType s.g56.r1796_ndataBuffer_5F2_5Fcf_5FexceptionVec_5F1 at old
  have port0 := idu_alu_access_faults_0 s i
  have port1 := idu_alu_access_faults_1 s i
  simp only [v30123, v2687, v30122, v30121, v30120, v30116, v9721, v28257, v28256, v28255, v30119, v30118, v30117, v28442, v28441, v28440, v28439, v29851, v24, v29850, v29849, v29848, v29844, v26362, v26361, v29847, v29846, v29845, v26370, v26369, v26368]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [AluAccessFaultsClear]
def QueueAluAccessFaults3 (s : State) : Prop := AluAccessFaultsClear s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType s.g57.r1851_ndataBuffer_5F3_5Fcf_5FexceptionVec_5F1
theorem queue_alu_access_faults3_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueAluAccessFaults3 (step s i) := by
  change AluAccessFaultsClear (v30563 s i) (v30291 s i)
  simp [v30563, v30291, reset, AluAccessFaultsClear, v24]
theorem queue_alu_access_faults3_step (s : State) (i : Inputs) (old : QueueAluAccessFaults3 s) :
    QueueAluAccessFaults3 (step s i) := by
  change AluAccessFaultsClear (v30563 s i) (v30291 s i)
  change AluAccessFaultsClear s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType s.g57.r1851_ndataBuffer_5F3_5Fcf_5FexceptionVec_5F1 at old
  have port0 := idu_alu_access_faults_0 s i
  have port1 := idu_alu_access_faults_1 s i
  simp only [v30563, v2687, v30562, v30561, v30560, v30556, v2750, v28257, v28256, v28255, v30559, v30558, v30557, v28442, v28441, v28440, v28439, v30291, v24, v30290, v30289, v30288, v30284, v26362, v26361, v30287, v30286, v30285, v26370, v26369, v26368]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [AluAccessFaultsClear]
def QueueAluAccessFaults (s : State) : Prop := QueueAluAccessFaults0 s ∧ QueueAluAccessFaults1 s ∧ QueueAluAccessFaults2 s ∧ QueueAluAccessFaults3 s
theorem queue_selected_alu_access_faults (s : State) (i : Inputs) (queue : QueueAluAccessFaults s) :
    AluAccessFaultsClear (v24912 s i) (v24402 s i) := by
  rcases queue with ⟨h0, h1, h2, h3⟩
  have bound := s.g59.r1900_nringBufferTail.isLt
  have cases : s.g59.r1900_nringBufferTail.toNat = 0 ∨ s.g59.r1900_nringBufferTail.toNat = 1 ∨ s.g59.r1900_nringBufferTail.toNat = 2 ∨ s.g59.r1900_nringBufferTail.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : s.g59.r1900_nringBufferTail = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, v24402, v24401, v24400, v24399, v24389, v24398, v24390, v24397, v24392, v24391, v24396, v24395, v24394, v24393, eq, QueueAluAccessFaults0] using h0
  · have eq : s.g59.r1900_nringBufferTail = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, v24402, v24401, v24400, v24399, v24389, v24398, v24390, v24397, v24392, v24391, v24396, v24395, v24394, v24393, eq, QueueAluAccessFaults1] using h1
  · have eq : s.g59.r1900_nringBufferTail = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, v24402, v24401, v24400, v24399, v24389, v24398, v24390, v24397, v24392, v24391, v24396, v24395, v24394, v24393, eq, QueueAluAccessFaults2] using h2
  · have eq : s.g59.r1900_nringBufferTail = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24912, v24911, v24910, v24909, v24899, v2750, v24908, v24900, v9721, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v110, v24402, v24401, v24400, v24399, v24389, v24398, v24390, v24397, v24392, v24391, v24396, v24395, v24394, v24393, eq, QueueAluAccessFaults3] using h3
def ExecuteAluAccessFaults (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 → AluAccessFaultsClear s.g48.r1553_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FfuType s.g47.r1519_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F1
theorem execute_alu_access_faults_step (s : State) (i : Inputs)
    (queue : QueueAluAccessFaults s) (old : ExecuteAluAccessFaults s) :
    ExecuteAluAccessFaults (step s i) := by
  intro valid
  change AluAccessFaultsClear (v24913 s i) (v24403 s i)
  by_cases fire : v24283 s i = 1
  · simpa only [v24913, v24403, fire, ↓reduceIte] using queue_selected_alu_access_faults s i queue
  · simp only [v24913, v24403, fire, ↓reduceIte]
    exact old (execute_valid_backward s i i valid fire)
def AluAccessFaultState (s : State) : Prop := QueueAluAccessFaults s ∧ ExecuteAluAccessFaults s
theorem alu_access_fault_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    AluAccessFaultState (step s i) := by
  constructor
  · exact ⟨queue_alu_access_faults0_reset s i reset, queue_alu_access_faults1_reset s i reset, queue_alu_access_faults2_reset s i reset, queue_alu_access_faults3_reset s i reset⟩
  · intro valid
    have zero := execute_valid_reset s i i reset
    change v6 (step s i) i = 1 at valid
    rw [zero] at valid
    contradiction
theorem alu_access_fault_step (s : State) (i : Inputs) (old : AluAccessFaultState s) :
    AluAccessFaultState (step s i) := by
  rcases old with ⟨queue, exu⟩
  refine ⟨?_, execute_alu_access_faults_step s i queue exu⟩
  rcases queue with ⟨h0, h1, h2, h3⟩
  exact ⟨queue_alu_access_faults0_step s i h0, queue_alu_access_faults1_step s i h1, queue_alu_access_faults2_step s i h2, queue_alu_access_faults3_step s i h3⟩
theorem alu_access_fault_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    AluAccessFaultState (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact alu_access_fault_reset initial (inputs 0) reset
  | succ t ih => exact alu_access_fault_step _ _ ih
#print axioms alu_access_fault_run
end NutShellProofs
