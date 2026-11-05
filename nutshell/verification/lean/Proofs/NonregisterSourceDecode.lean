import Proofs.InstructionWidth
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def NonregisterSourceDecoded (bit : Nat) (instr : BitVec 64) (kind : BitVec 1) (addr : BitVec 5) : Prop :=
  kind = 1 → addr = 0


def QueueNonregisterSource1_0 (s : State) : Prop :=
  NonregisterSourceDecoded 15 s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g53.r1718_ndataBuffer_5F0_5Fctrl_5Fsrc1Type s.g53.r1722_ndataBuffer_5F0_5Fctrl_5FrfSrc1

theorem queue_nonregister_source1_0_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueNonregisterSource1_0 (step s i) := by
  change NonregisterSourceDecoded 15 (v26233 s i) (v28034 s i) (v28866 s i)
  simp [NonregisterSourceDecoded, v26233, v28034, v28866, reset, v24, v4051, v15076]

theorem queue_nonregister_source1_0_step (s : State) (i : Inputs) (old : QueueNonregisterSource1_0 s) :
    QueueNonregisterSource1_0 (step s i) := by
  change NonregisterSourceDecoded 15 (v26233 s i) (v28034 s i) (v28866 s i)
  change NonregisterSourceDecoded 15 s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g53.r1718_ndataBuffer_5F0_5Fctrl_5Fsrc1Type s.g53.r1722_ndataBuffer_5F0_5Fctrl_5FrfSrc1 at old
  unfold NonregisterSourceDecoded at *
  simp only [v26233, v4051, v26232, v26231, v26230, v26208, v26203, v26213, v26212, v26211, v26229, v26228, v26221, v26216, v26227, v26226, v26225, v26224, v28034, v24, v28033, v28032, v28031, v27995, v27994, v28010, v28009, v28008, v28007, v27998, v27996, v27997, v28030, v28029, v28012, v28011, v28028, v28027, v28026, v28025, v28024, v28015, v28013, v28014, v28866, v15076, v28865, v28864, v28863, v28845, v28844, v28851, v28850, v28849, v28848, v28846, v110, v28847, v28623, v28862, v28861, v28853, v28852, v28860, v28859, v28858, v28857, v28856, v28854, v28855, v28816]
  repeat' first | (split <;> try simp_all only [↓reduceIte]) | (intro h; try simp_all) | assumption
  all_goals try simp_all
  all_goals decide

def QueueNonregisterSource1_1 (s : State) : Prop :=
  NonregisterSourceDecoded 15 s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g55.r1773_ndataBuffer_5F1_5Fctrl_5Fsrc1Type s.g55.r1777_ndataBuffer_5F1_5Fctrl_5FrfSrc1

theorem queue_nonregister_source1_1_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueNonregisterSource1_1 (step s i) := by
  change NonregisterSourceDecoded 15 (v29247 s i) (v29637 s i) (v29677 s i)
  simp [NonregisterSourceDecoded, v29247, v29637, v29677, reset, v24, v4051, v15076]

theorem queue_nonregister_source1_1_step (s : State) (i : Inputs) (old : QueueNonregisterSource1_1 s) :
    QueueNonregisterSource1_1 (step s i) := by
  change NonregisterSourceDecoded 15 (v29247 s i) (v29637 s i) (v29677 s i)
  change NonregisterSourceDecoded 15 s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g55.r1773_ndataBuffer_5F1_5Fctrl_5Fsrc1Type s.g55.r1777_ndataBuffer_5F1_5Fctrl_5FrfSrc1 at old
  unfold NonregisterSourceDecoded at *
  simp only [v29247, v4051, v29246, v29245, v29244, v29239, v29238, v26213, v26212, v26211, v29243, v29242, v29241, v29240, v26227, v26226, v26225, v26224, v29637, v24, v29636, v29635, v29634, v29629, v29628, v28010, v28009, v28008, v28007, v27998, v27996, v27997, v29633, v29632, v29631, v29630, v28028, v28027, v28026, v28025, v28024, v28015, v28013, v28014, v29677, v15076, v29676, v29675, v29674, v29669, v29668, v28851, v28850, v28849, v28848, v28846, v110, v28847, v28623, v29673, v29672, v29671, v29670, v28860, v28859, v28858, v28857, v28856, v28854, v28855, v28816]
  repeat' first | (split <;> try simp_all only [↓reduceIte]) | (intro h; try simp_all) | assumption
  all_goals try simp_all
  all_goals decide

def QueueNonregisterSource1_2 (s : State) : Prop :=
  NonregisterSourceDecoded 15 s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g57.r1828_ndataBuffer_5F2_5Fctrl_5Fsrc1Type s.g57.r1832_ndataBuffer_5F2_5Fctrl_5FrfSrc1

theorem queue_nonregister_source1_2_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueNonregisterSource1_2 (step s i) := by
  change NonregisterSourceDecoded 15 (v29795 s i) (v30107 s i) (v30139 s i)
  simp [NonregisterSourceDecoded, v29795, v30107, v30139, reset, v24, v4051, v15076]

theorem queue_nonregister_source1_2_step (s : State) (i : Inputs) (old : QueueNonregisterSource1_2 s) :
    QueueNonregisterSource1_2 (step s i) := by
  change NonregisterSourceDecoded 15 (v29795 s i) (v30107 s i) (v30139 s i)
  change NonregisterSourceDecoded 15 s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g57.r1828_ndataBuffer_5F2_5Fctrl_5Fsrc1Type s.g57.r1832_ndataBuffer_5F2_5Fctrl_5FrfSrc1 at old
  unfold NonregisterSourceDecoded at *
  simp only [v29795, v4051, v29794, v29793, v29792, v29788, v9721, v26213, v26212, v26211, v29791, v29790, v29789, v26227, v26226, v26225, v26224, v30107, v24, v30106, v30105, v30104, v30100, v28010, v28009, v28008, v28007, v27998, v27996, v27997, v30103, v30102, v30101, v28028, v28027, v28026, v28025, v28024, v28015, v28013, v28014, v30139, v15076, v30138, v30137, v30136, v30132, v28851, v28850, v28849, v28848, v28846, v110, v28847, v28623, v30135, v30134, v30133, v28860, v28859, v28858, v28857, v28856, v28854, v28855, v28816]
  repeat' first | (split <;> try simp_all only [↓reduceIte]) | (intro h; try simp_all) | assumption
  all_goals try simp_all
  all_goals decide

def QueueNonregisterSource1_3 (s : State) : Prop :=
  NonregisterSourceDecoded 15 s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g58.r1883_ndataBuffer_5F3_5Fctrl_5Fsrc1Type s.g58.r1887_ndataBuffer_5F3_5Fctrl_5FrfSrc1

theorem queue_nonregister_source1_3_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueNonregisterSource1_3 (step s i) := by
  change NonregisterSourceDecoded 15 (v30235 s i) (v30547 s i) (v30579 s i)
  simp [NonregisterSourceDecoded, v30235, v30547, v30579, reset, v24, v4051, v15076]

theorem queue_nonregister_source1_3_step (s : State) (i : Inputs) (old : QueueNonregisterSource1_3 s) :
    QueueNonregisterSource1_3 (step s i) := by
  change NonregisterSourceDecoded 15 (v30235 s i) (v30547 s i) (v30579 s i)
  change NonregisterSourceDecoded 15 s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g58.r1883_ndataBuffer_5F3_5Fctrl_5Fsrc1Type s.g58.r1887_ndataBuffer_5F3_5Fctrl_5FrfSrc1 at old
  unfold NonregisterSourceDecoded at *
  simp only [v30235, v4051, v30234, v30233, v30232, v30228, v2750, v26213, v26212, v26211, v30231, v30230, v30229, v26227, v26226, v26225, v26224, v30547, v24, v30546, v30545, v30544, v30540, v28010, v28009, v28008, v28007, v27998, v27996, v27997, v30543, v30542, v30541, v28028, v28027, v28026, v28025, v28024, v28015, v28013, v28014, v30579, v15076, v30578, v30577, v30576, v30572, v28851, v28850, v28849, v28848, v28846, v110, v28847, v28623, v30575, v30574, v30573, v28860, v28859, v28858, v28857, v28856, v28854, v28855, v28816]
  repeat' first | (split <;> try simp_all only [↓reduceIte]) | (intro h; try simp_all) | assumption
  all_goals try simp_all
  all_goals decide

def QueueNonregisterSource2_0 (s : State) : Prop :=
  NonregisterSourceDecoded 20 s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g53.r1719_ndataBuffer_5F0_5Fctrl_5Fsrc2Type s.g53.r1723_ndataBuffer_5F0_5Fctrl_5FrfSrc2

theorem queue_nonregister_source2_0_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueNonregisterSource2_0 (step s i) := by
  change NonregisterSourceDecoded 20 (v26233 s i) (v28073 s i) (v28891 s i)
  simp [NonregisterSourceDecoded, v26233, v28073, v28891, reset, v24, v4051, v15076]

theorem queue_nonregister_source2_0_step (s : State) (i : Inputs) (old : QueueNonregisterSource2_0 s) :
    QueueNonregisterSource2_0 (step s i) := by
  change NonregisterSourceDecoded 20 (v26233 s i) (v28073 s i) (v28891 s i)
  change NonregisterSourceDecoded 20 s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g53.r1719_ndataBuffer_5F0_5Fctrl_5Fsrc2Type s.g53.r1723_ndataBuffer_5F0_5Fctrl_5FrfSrc2 at old
  unfold NonregisterSourceDecoded at *
  simp only [v26233, v4051, v26232, v26231, v26230, v26208, v26203, v26213, v26212, v26211, v26229, v26228, v26221, v26216, v26227, v26226, v26225, v26224, v28073, v24, v28072, v28071, v28070, v28036, v28035, v28050, v28049, v28048, v28069, v28068, v28052, v28051, v28067, v28066, v28065, v28064, v28891, v15076, v28890, v28889, v28888, v28868, v28867, v28875, v28874, v28873, v28872, v28869, v28870, v28871, v28887, v28886, v28877, v28876, v28885, v28884, v28883, v28882, v28881, v28878, v28879, v28880]
  repeat' first | (split <;> try simp_all only [↓reduceIte]) | (intro h; try simp_all) | assumption
  all_goals try simp_all
  all_goals decide

def QueueNonregisterSource2_1 (s : State) : Prop :=
  NonregisterSourceDecoded 20 s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g55.r1774_ndataBuffer_5F1_5Fctrl_5Fsrc2Type s.g55.r1778_ndataBuffer_5F1_5Fctrl_5FrfSrc2

theorem queue_nonregister_source2_1_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueNonregisterSource2_1 (step s i) := by
  change NonregisterSourceDecoded 20 (v29247 s i) (v29647 s i) (v29687 s i)
  simp [NonregisterSourceDecoded, v29247, v29647, v29687, reset, v24, v4051, v15076]

theorem queue_nonregister_source2_1_step (s : State) (i : Inputs) (old : QueueNonregisterSource2_1 s) :
    QueueNonregisterSource2_1 (step s i) := by
  change NonregisterSourceDecoded 20 (v29247 s i) (v29647 s i) (v29687 s i)
  change NonregisterSourceDecoded 20 s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g55.r1774_ndataBuffer_5F1_5Fctrl_5Fsrc2Type s.g55.r1778_ndataBuffer_5F1_5Fctrl_5FrfSrc2 at old
  unfold NonregisterSourceDecoded at *
  simp only [v29247, v4051, v29246, v29245, v29244, v29239, v29238, v26213, v26212, v26211, v29243, v29242, v29241, v29240, v26227, v26226, v26225, v26224, v29647, v24, v29646, v29645, v29644, v29639, v29638, v28050, v28049, v28048, v29643, v29642, v29641, v29640, v28067, v28066, v28065, v28064, v29687, v15076, v29686, v29685, v29684, v29679, v29678, v28875, v28874, v28873, v28872, v28869, v28870, v28871, v29683, v29682, v29681, v29680, v28885, v28884, v28883, v28882, v28881, v28878, v28879, v28880]
  repeat' first | (split <;> try simp_all only [↓reduceIte]) | (intro h; try simp_all) | assumption
  all_goals try simp_all
  all_goals decide

def QueueNonregisterSource2_2 (s : State) : Prop :=
  NonregisterSourceDecoded 20 s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g57.r1829_ndataBuffer_5F2_5Fctrl_5Fsrc2Type s.g57.r1833_ndataBuffer_5F2_5Fctrl_5FrfSrc2

theorem queue_nonregister_source2_2_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueNonregisterSource2_2 (step s i) := by
  change NonregisterSourceDecoded 20 (v29795 s i) (v30115 s i) (v30147 s i)
  simp [NonregisterSourceDecoded, v29795, v30115, v30147, reset, v24, v4051, v15076]

theorem queue_nonregister_source2_2_step (s : State) (i : Inputs) (old : QueueNonregisterSource2_2 s) :
    QueueNonregisterSource2_2 (step s i) := by
  change NonregisterSourceDecoded 20 (v29795 s i) (v30115 s i) (v30147 s i)
  change NonregisterSourceDecoded 20 s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g57.r1829_ndataBuffer_5F2_5Fctrl_5Fsrc2Type s.g57.r1833_ndataBuffer_5F2_5Fctrl_5FrfSrc2 at old
  unfold NonregisterSourceDecoded at *
  simp only [v29795, v4051, v29794, v29793, v29792, v29788, v9721, v26213, v26212, v26211, v29791, v29790, v29789, v26227, v26226, v26225, v26224, v30115, v24, v30114, v30113, v30112, v30108, v28050, v28049, v28048, v30111, v30110, v30109, v28067, v28066, v28065, v28064, v30147, v15076, v30146, v30145, v30144, v30140, v28875, v28874, v28873, v28872, v28869, v28870, v28871, v30143, v30142, v30141, v28885, v28884, v28883, v28882, v28881, v28878, v28879, v28880]
  repeat' first | (split <;> try simp_all only [↓reduceIte]) | (intro h; try simp_all) | assumption
  all_goals try simp_all
  all_goals decide

def QueueNonregisterSource2_3 (s : State) : Prop :=
  NonregisterSourceDecoded 20 s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g58.r1884_ndataBuffer_5F3_5Fctrl_5Fsrc2Type s.g59.r1888_ndataBuffer_5F3_5Fctrl_5FrfSrc2

theorem queue_nonregister_source2_3_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueNonregisterSource2_3 (step s i) := by
  change NonregisterSourceDecoded 20 (v30235 s i) (v30555 s i) (v30587 s i)
  simp [NonregisterSourceDecoded, v30235, v30555, v30587, reset, v24, v4051, v15076]

theorem queue_nonregister_source2_3_step (s : State) (i : Inputs) (old : QueueNonregisterSource2_3 s) :
    QueueNonregisterSource2_3 (step s i) := by
  change NonregisterSourceDecoded 20 (v30235 s i) (v30555 s i) (v30587 s i)
  change NonregisterSourceDecoded 20 s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g58.r1884_ndataBuffer_5F3_5Fctrl_5Fsrc2Type s.g59.r1888_ndataBuffer_5F3_5Fctrl_5FrfSrc2 at old
  unfold NonregisterSourceDecoded at *
  simp only [v30235, v4051, v30234, v30233, v30232, v30228, v2750, v26213, v26212, v26211, v30231, v30230, v30229, v26227, v26226, v26225, v26224, v30555, v24, v30554, v30553, v30552, v30548, v28050, v28049, v28048, v30551, v30550, v30549, v28067, v28066, v28065, v28064, v30587, v15076, v30586, v30585, v30584, v30580, v28875, v28874, v28873, v28872, v28869, v28870, v28871, v30583, v30582, v30581, v28885, v28884, v28883, v28882, v28881, v28878, v28879, v28880]
  repeat' first | (split <;> try simp_all only [↓reduceIte]) | (intro h; try simp_all) | assumption
  all_goals try simp_all
  all_goals decide

def QueueNonregisterSources1Decoded (s : State) : Prop :=
  QueueNonregisterSource1_0 s ∧ QueueNonregisterSource1_1 s ∧ QueueNonregisterSource1_2 s ∧ QueueNonregisterSource1_3 s

theorem queue_selected_nonregister_source1 (s : State) (i : Inputs) (queue : QueueNonregisterSources1Decoded s) :
    NonregisterSourceDecoded 15 (v24297 s i) (v24881 s i) (v11723 s i) := by
  rcases queue with ⟨h0, h1, h2, h3⟩
  have bound := s.g59.r1900_nringBufferTail.isLt
  have cases : s.g59.r1900_nringBufferTail.toNat = 0 ∨ s.g59.r1900_nringBufferTail.toNat = 1 ∨ s.g59.r1900_nringBufferTail.toNat = 2 ∨ s.g59.r1900_nringBufferTail.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : s.g59.r1900_nringBufferTail = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24881, v24880, v24879, v24869, v24878, v24870, v24877, v24872, v24871, v24876, v24875, v24874, v24873, v11723, v11722, v11721, v11711, v11720, v11712, v11719, v11714, v11713, v11718, v11717, v11716, v11715, eq, QueueNonregisterSource1_0] using h0
  · have eq : s.g59.r1900_nringBufferTail = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24881, v24880, v24879, v24869, v24878, v24870, v24877, v24872, v24871, v24876, v24875, v24874, v24873, v11723, v11722, v11721, v11711, v11720, v11712, v11719, v11714, v11713, v11718, v11717, v11716, v11715, eq, QueueNonregisterSource1_1] using h1
  · have eq : s.g59.r1900_nringBufferTail = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24881, v24880, v24879, v24869, v24878, v24870, v24877, v24872, v24871, v24876, v24875, v24874, v24873, v11723, v11722, v11721, v11711, v11720, v11712, v11719, v11714, v11713, v11718, v11717, v11716, v11715, eq, QueueNonregisterSource1_2] using h2
  · have eq : s.g59.r1900_nringBufferTail = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24881, v24880, v24879, v24869, v24878, v24870, v24877, v24872, v24871, v24876, v24875, v24874, v24873, v11723, v11722, v11721, v11711, v11720, v11712, v11719, v11714, v11713, v11718, v11717, v11716, v11715, eq, QueueNonregisterSource1_3] using h3

def ExecuteNonregisterSource1Decoded (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 → NonregisterSourceDecoded 15 s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr s.g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type s.g48.r1555_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc1

theorem execute_nonregister_source1_step (s : State) (i : Inputs)
    (queue : QueueNonregisterSources1Decoded s) (old : ExecuteNonregisterSource1Decoded s) :
    ExecuteNonregisterSource1Decoded (step s i) := by
  intro valid
  change NonregisterSourceDecoded 15 (v24298 s i) (v24883 s i) (v24930 s i)
  by_cases fire : v24283 s i = 1
  · simpa only [v24298, v24883, v24930, fire, ↓reduceIte, v24882, v24897, v24929, v24931] using queue_selected_nonregister_source1 s i queue
  · simp only [v24298, v24883, v24930, fire, ↓reduceIte]
    exact old (execute_valid_backward s i i valid fire)

def NonregisterSource1DecodeState (s : State) : Prop := QueueNonregisterSources1Decoded s ∧ ExecuteNonregisterSource1Decoded s

theorem nonregister_source1_decode_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    NonregisterSource1DecodeState (step s i) := by
  constructor
  · exact ⟨queue_nonregister_source1_0_reset s i reset, queue_nonregister_source1_1_reset s i reset, queue_nonregister_source1_2_reset s i reset, queue_nonregister_source1_3_reset s i reset⟩
  · intro valid
    have zero := execute_valid_reset s i i reset
    change v6 (step s i) i = 1 at valid
    rw [zero] at valid
    contradiction

theorem nonregister_source1_decode_step (s : State) (i : Inputs) (old : NonregisterSource1DecodeState s) :
    NonregisterSource1DecodeState (step s i) := by
  rcases old with ⟨queue, exu⟩
  refine ⟨?_, execute_nonregister_source1_step s i queue exu⟩
  rcases queue with ⟨h0, h1, h2, h3⟩
  exact ⟨queue_nonregister_source1_0_step s i h0, queue_nonregister_source1_1_step s i h1, queue_nonregister_source1_2_step s i h2, queue_nonregister_source1_3_step s i h3⟩

theorem nonregister_source1_decode_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    NonregisterSource1DecodeState (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact nonregister_source1_decode_reset initial (inputs 0) reset
  | succ t ih => exact nonregister_source1_decode_step _ _ ih

#print axioms nonregister_source1_decode_run

def QueueNonregisterSources2Decoded (s : State) : Prop :=
  QueueNonregisterSource2_0 s ∧ QueueNonregisterSource2_1 s ∧ QueueNonregisterSource2_2 s ∧ QueueNonregisterSource2_3 s

theorem queue_selected_nonregister_source2 (s : State) (i : Inputs) (queue : QueueNonregisterSources2Decoded s) :
    NonregisterSourceDecoded 20 (v24297 s i) (v24896 s i) (v11765 s i) := by
  rcases queue with ⟨h0, h1, h2, h3⟩
  have bound := s.g59.r1900_nringBufferTail.isLt
  have cases : s.g59.r1900_nringBufferTail.toNat = 0 ∨ s.g59.r1900_nringBufferTail.toNat = 1 ∨ s.g59.r1900_nringBufferTail.toNat = 2 ∨ s.g59.r1900_nringBufferTail.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : s.g59.r1900_nringBufferTail = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24896, v24895, v24894, v24884, v24893, v24885, v24892, v24887, v24886, v24891, v24890, v24889, v24888, v11765, v11764, v11763, v11753, v11762, v11754, v11761, v11756, v11755, v11760, v11759, v11758, v11757, eq, QueueNonregisterSource2_0] using h0
  · have eq : s.g59.r1900_nringBufferTail = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24896, v24895, v24894, v24884, v24893, v24885, v24892, v24887, v24886, v24891, v24890, v24889, v24888, v11765, v11764, v11763, v11753, v11762, v11754, v11761, v11756, v11755, v11760, v11759, v11758, v11757, eq, QueueNonregisterSource2_1] using h1
  · have eq : s.g59.r1900_nringBufferTail = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24896, v24895, v24894, v24884, v24893, v24885, v24892, v24887, v24886, v24891, v24890, v24889, v24888, v11765, v11764, v11763, v11753, v11762, v11754, v11761, v11756, v11755, v11760, v11759, v11758, v11757, eq, QueueNonregisterSource2_2] using h2
  · have eq : s.g59.r1900_nringBufferTail = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24896, v24895, v24894, v24884, v24893, v24885, v24892, v24887, v24886, v24891, v24890, v24889, v24888, v11765, v11764, v11763, v11753, v11762, v11754, v11761, v11756, v11755, v11760, v11759, v11758, v11757, eq, QueueNonregisterSource2_3] using h3

def ExecuteNonregisterSource2Decoded (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 → NonregisterSourceDecoded 20 s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr s.g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type s.g48.r1556_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc2

theorem execute_nonregister_source2_step (s : State) (i : Inputs)
    (queue : QueueNonregisterSources2Decoded s) (old : ExecuteNonregisterSource2Decoded s) :
    ExecuteNonregisterSource2Decoded (step s i) := by
  intro valid
  change NonregisterSourceDecoded 20 (v24298 s i) (v24898 s i) (v24932 s i)
  by_cases fire : v24283 s i = 1
  · simpa only [v24298, v24898, v24932, fire, ↓reduceIte, v24882, v24897, v24929, v24931] using queue_selected_nonregister_source2 s i queue
  · simp only [v24298, v24898, v24932, fire, ↓reduceIte]
    exact old (execute_valid_backward s i i valid fire)

def NonregisterSource2DecodeState (s : State) : Prop := QueueNonregisterSources2Decoded s ∧ ExecuteNonregisterSource2Decoded s

theorem nonregister_source2_decode_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    NonregisterSource2DecodeState (step s i) := by
  constructor
  · exact ⟨queue_nonregister_source2_0_reset s i reset, queue_nonregister_source2_1_reset s i reset, queue_nonregister_source2_2_reset s i reset, queue_nonregister_source2_3_reset s i reset⟩
  · intro valid
    have zero := execute_valid_reset s i i reset
    change v6 (step s i) i = 1 at valid
    rw [zero] at valid
    contradiction

theorem nonregister_source2_decode_step (s : State) (i : Inputs) (old : NonregisterSource2DecodeState s) :
    NonregisterSource2DecodeState (step s i) := by
  rcases old with ⟨queue, exu⟩
  refine ⟨?_, execute_nonregister_source2_step s i queue exu⟩
  rcases queue with ⟨h0, h1, h2, h3⟩
  exact ⟨queue_nonregister_source2_0_step s i h0, queue_nonregister_source2_1_step s i h1, queue_nonregister_source2_2_step s i h2, queue_nonregister_source2_3_step s i h3⟩

theorem nonregister_source2_decode_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    NonregisterSource2DecodeState (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact nonregister_source2_decode_reset initial (inputs 0) reset
  | succ t ih => exact nonregister_source2_decode_step _ _ ih

#print axioms nonregister_source2_decode_run
end NutShellProofs
