import Proofs.UpperLegalDecode
import Proofs.InstructionWidth
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Conditional upper dispatch carries no illegal-instruction exception. -/
def UpperLegal (instr : BitVec 64) (unit : BitVec 3) (illegal : BitVec 1) : Prop :=
  ∀ operation, IsUpperImmediate operation instr → unit = 0 → illegal = 0

theorem idu_upper_legal_0 (s : State) (i : Inputs) :
    UpperLegal (v26210 s i) (v28254 s i) (v26905 s i) := by
  intro operation matched alu
  have inactive : v28077 s i ≠ 1 := by
    intro active
    simp [v28254, active, v28078] at alu
  have bound := (v28077 s i).isLt
  have normal : v26384 s i = 0 := by
    change v28077 s i = 0
    have neq : (v28077 s i).toNat ≠ 1 := by
      intro eq
      apply inactive
      exact BitVec.eq_of_toNat_eq (by simpa using eq)
    apply BitVec.eq_of_toNat_eq
    change _ = 0
    omega
  cases operation with
  | lui => exact (idu_upper_0_lui_legal s i normal matched)
  | auipc => exact (idu_upper_0_auipc_legal s i normal matched)
theorem idu_upper_legal_1 (s : State) (i : Inputs) :
    UpperLegal (v26223 s i) (v28438 s i) (v27432 s i) := by
  intro operation matched alu
  have inactive : v28261 s i ≠ 1 := by
    intro active
    simp [v28438, active, v28262] at alu
  have bound := (v28261 s i).isLt
  have normal : v26911 s i = 0 := by
    change v28261 s i = 0
    have neq : (v28261 s i).toNat ≠ 1 := by
      intro eq
      apply inactive
      exact BitVec.eq_of_toNat_eq (by simpa using eq)
    apply BitVec.eq_of_toNat_eq
    change _ = 0
    omega
  cases operation with
  | lui => exact (idu_upper_1_lui_legal s i normal matched)
  | auipc => exact (idu_upper_1_auipc_legal s i normal matched)
def QueueUpperLegal0 (s : State) : Prop :=
  UpperLegal s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType s.g52.r1687_ndataBuffer_5F0_5Fcf_5FexceptionVec_5F2
theorem queue_upper_legal0_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueUpperLegal0 (step s i) := by
  change UpperLegal (v26233 s i) (v28448 s i) (v27439 s i)
  intro operation; cases operation <;> simp [IsUpperImmediate, UpperImmediateOp.encoding, UpperImmediateOp.mask, v26233, v28448, v27439, reset, v4051]
theorem queue_upper_legal0_step (s : State) (i : Inputs) (old : QueueUpperLegal0 s) :
    QueueUpperLegal0 (step s i) := by
  change UpperLegal (v26233 s i) (v28448 s i) (v27439 s i)
  change UpperLegal s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType s.g52.r1687_ndataBuffer_5F0_5Fcf_5FexceptionVec_5F2 at old
  have port0 := idu_upper_legal_0 s i
  have port1 := idu_upper_legal_1 s i
  simp only [v26233, v4051, v26232, v26231, v26230, v26208, v26203, v26213, v26212, v26211, v26229, v26228, v26221, v26216, v26227, v26226, v26225, v26224, v28448, v2687, v28447, v28446, v28445, v28075, v28074, v28257, v28256, v28255, v28444, v28443, v28259, v28258, v28442, v28441, v28440, v28439, v27439, v24, v27438, v27437, v27436, v26378, v26377, v27435, v27434, v26907, v26906, v27433]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals intro operation; cases operation <;> simp_all [IsUpperImmediate, UpperImmediateOp.encoding]

def QueueUpperLegal1 (s : State) : Prop :=
  UpperLegal s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType s.g54.r1742_ndataBuffer_5F1_5Fcf_5FexceptionVec_5F2
theorem queue_upper_legal1_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueUpperLegal1 (step s i) := by
  change UpperLegal (v29247 s i) (v29657 s i) (v29327 s i)
  intro operation; cases operation <;> simp [IsUpperImmediate, UpperImmediateOp.encoding, UpperImmediateOp.mask, v29247, v29657, v29327, reset, v4051]
theorem queue_upper_legal1_step (s : State) (i : Inputs) (old : QueueUpperLegal1 s) :
    QueueUpperLegal1 (step s i) := by
  change UpperLegal (v29247 s i) (v29657 s i) (v29327 s i)
  change UpperLegal s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType s.g54.r1742_ndataBuffer_5F1_5Fcf_5FexceptionVec_5F2 at old
  have port0 := idu_upper_legal_0 s i
  have port1 := idu_upper_legal_1 s i
  simp only [v29247, v4051, v29246, v29245, v29244, v29239, v29238, v26213, v26212, v26211, v29243, v29242, v29241, v29240, v26227, v26226, v26225, v26224, v29657, v2687, v29656, v29655, v29654, v29649, v29648, v28257, v28256, v28255, v29653, v29652, v29651, v29650, v28442, v28441, v28440, v28439, v29327, v24, v29326, v29325, v29324, v29319, v29318, v29323, v29322, v29321, v29320, v27433]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals intro operation; cases operation <;> simp_all [IsUpperImmediate, UpperImmediateOp.encoding]

def QueueUpperLegal2 (s : State) : Prop :=
  UpperLegal s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType s.g56.r1797_ndataBuffer_5F2_5Fcf_5FexceptionVec_5F2
theorem queue_upper_legal2_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueUpperLegal2 (step s i) := by
  change UpperLegal (v29795 s i) (v30123 s i) (v29859 s i)
  intro operation; cases operation <;> simp [IsUpperImmediate, UpperImmediateOp.encoding, UpperImmediateOp.mask, v29795, v30123, v29859, reset, v4051]
theorem queue_upper_legal2_step (s : State) (i : Inputs) (old : QueueUpperLegal2 s) :
    QueueUpperLegal2 (step s i) := by
  change UpperLegal (v29795 s i) (v30123 s i) (v29859 s i)
  change UpperLegal s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType s.g56.r1797_ndataBuffer_5F2_5Fcf_5FexceptionVec_5F2 at old
  have port0 := idu_upper_legal_0 s i
  have port1 := idu_upper_legal_1 s i
  simp only [v29795, v4051, v29794, v29793, v29792, v29788, v9721, v26213, v26212, v26211, v29791, v29790, v29789, v26227, v26226, v26225, v26224, v30123, v2687, v30122, v30121, v30120, v30116, v28257, v28256, v28255, v30119, v30118, v30117, v28442, v28441, v28440, v28439, v29859, v24, v29858, v29857, v29856, v29852, v29855, v29854, v29853, v27433]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals intro operation; cases operation <;> simp_all [IsUpperImmediate, UpperImmediateOp.encoding]

def QueueUpperLegal3 (s : State) : Prop :=
  UpperLegal s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType s.g57.r1852_ndataBuffer_5F3_5Fcf_5FexceptionVec_5F2
theorem queue_upper_legal3_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueUpperLegal3 (step s i) := by
  change UpperLegal (v30235 s i) (v30563 s i) (v30299 s i)
  intro operation; cases operation <;> simp [IsUpperImmediate, UpperImmediateOp.encoding, UpperImmediateOp.mask, v30235, v30563, v30299, reset, v4051]
theorem queue_upper_legal3_step (s : State) (i : Inputs) (old : QueueUpperLegal3 s) :
    QueueUpperLegal3 (step s i) := by
  change UpperLegal (v30235 s i) (v30563 s i) (v30299 s i)
  change UpperLegal s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType s.g57.r1852_ndataBuffer_5F3_5Fcf_5FexceptionVec_5F2 at old
  have port0 := idu_upper_legal_0 s i
  have port1 := idu_upper_legal_1 s i
  simp only [v30235, v4051, v30234, v30233, v30232, v30228, v2750, v26213, v26212, v26211, v30231, v30230, v30229, v26227, v26226, v26225, v26224, v30563, v2687, v30562, v30561, v30560, v30556, v28257, v28256, v28255, v30559, v30558, v30557, v28442, v28441, v28440, v28439, v30299, v24, v30298, v30297, v30296, v30292, v30295, v30294, v30293, v27433]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals intro operation; cases operation <;> simp_all [IsUpperImmediate, UpperImmediateOp.encoding]

def QueueUpperLegalLegal (s : State) : Prop :=
  QueueUpperLegal0 s ∧ QueueUpperLegal1 s ∧ QueueUpperLegal2 s ∧ QueueUpperLegal3 s
theorem queue_selected_upper_legal (s : State) (i : Inputs) (queue : QueueUpperLegalLegal s) :
    UpperLegal (v24297 s i) (v24912 s i) (v24417 s i) := by
  rcases queue with ⟨h0, h1, h2, h3⟩
  have bound := s.g59.r1900_nringBufferTail.isLt
  have cases : s.g59.r1900_nringBufferTail.toNat = 0 ∨ s.g59.r1900_nringBufferTail.toNat = 1 ∨ s.g59.r1900_nringBufferTail.toNat = 2 ∨ s.g59.r1900_nringBufferTail.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : s.g59.r1900_nringBufferTail = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v24417, v24416, v24415, v24414, v24404, v24413, v24405, v24412, v24407, v24406, v24411, v24410, v24409, v24408, eq, QueueUpperLegal0] using h0
  · have eq : s.g59.r1900_nringBufferTail = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v24417, v24416, v24415, v24414, v24404, v24413, v24405, v24412, v24407, v24406, v24411, v24410, v24409, v24408, eq, QueueUpperLegal1] using h1
  · have eq : s.g59.r1900_nringBufferTail = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v24417, v24416, v24415, v24414, v24404, v24413, v24405, v24412, v24407, v24406, v24411, v24410, v24409, v24408, eq, QueueUpperLegal2] using h2
  · have eq : s.g59.r1900_nringBufferTail = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v24417, v24416, v24415, v24414, v24404, v24413, v24405, v24412, v24407, v24406, v24411, v24410, v24409, v24408, eq, QueueUpperLegal3] using h3
def ExecuteUpperLegalLegal (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 → UpperLegal s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr s.g48.r1553_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FfuType s.g47.r1520_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F2
theorem execute_upper_legal_step (s : State) (i : Inputs)
    (queue : QueueUpperLegalLegal s) (old : ExecuteUpperLegalLegal s) :
    ExecuteUpperLegalLegal (step s i) := by
  intro valid
  change UpperLegal (v24298 s i) (v24913 s i) (v24418 s i)
  by_cases fire : v24283 s i = 1
  · simpa only [v24298, v24913, v24418, fire, ↓reduceIte] using queue_selected_upper_legal s i queue
  · simp only [v24298, v24913, v24418, fire, ↓reduceIte]
    exact old (execute_valid_backward s i i valid fire)
def UpperLegalState (s : State) : Prop := QueueUpperLegalLegal s ∧ ExecuteUpperLegalLegal s
theorem upper_legal_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    UpperLegalState (step s i) := by
  constructor
  · exact ⟨queue_upper_legal0_reset s i reset, queue_upper_legal1_reset s i reset, queue_upper_legal2_reset s i reset, queue_upper_legal3_reset s i reset⟩
  · intro valid
    have zero := execute_valid_reset s i i reset
    change v6 (step s i) i = 1 at valid
    rw [zero] at valid
    contradiction
theorem upper_legal_step (s : State) (i : Inputs) (old : UpperLegalState s) :
    UpperLegalState (step s i) := by
  rcases old with ⟨queue, exu⟩
  refine ⟨?_, execute_upper_legal_step s i queue exu⟩
  rcases queue with ⟨h0, h1, h2, h3⟩
  exact ⟨queue_upper_legal0_step s i h0, queue_upper_legal1_step s i h1, queue_upper_legal2_step s i h2, queue_upper_legal3_step s i h3⟩
theorem upper_legal_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    UpperLegalState (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact upper_legal_reset initial (inputs 0) reset
  | succ t ih => exact upper_legal_step _ _ ih
#print axioms upper_legal_run
end NutShellProofs
