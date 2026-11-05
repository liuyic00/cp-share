import Proofs.AddiDecode
import Proofs.InstructionWidth
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- ADDI dispatched to the ALU has its standard control and immediate semantics.
Exceptional decoding dispatches to a different unit and is not assumed absent. -/
def AddiDecoded (instr : BitVec 64) (unit : BitVec 3) (op : BitVec 7)
    (kind1 kind2 : BitVec 1) (imm : BitVec 64) (write : BitVec 1) : Prop :=
  IsADDI instr → unit = 0 →
    op = 64 ∧ kind1 = 0 ∧ kind2 = 1 ∧ imm = immediateI instr ∧ write = 1

theorem idu_addi_decoded_0 (s : State) (i : Inputs) :
    AddiDecoded (v26210 s i) (v28254 s i) (v28643 s i) (v28010 s i) (v28050 s i) (v29154 s i) (v28897 s i) := by
  intro addi alu
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
  exact ⟨idu_addi_0_operation s i normal addi, idu_addi_0_source1 s i normal addi, idu_addi_0_source2 s i normal addi, idu_addi_0_immediate s i normal addi, idu_addi_0_write s i normal addi⟩

theorem idu_addi_decoded_1 (s : State) (i : Inputs) :
    AddiDecoded (v26223 s i) (v28438 s i) (v28836 s i) (v28027 s i) (v28066 s i) (v29230 s i) (v28903 s i) := by
  intro addi alu
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
  exact ⟨idu_addi_1_operation s i normal addi, idu_addi_1_source1 s i normal addi, idu_addi_1_source2 s i normal addi, idu_addi_1_immediate s i normal addi, idu_addi_1_write s i normal addi⟩

def QueueAddi0 (s : State) : Prop :=
  AddiDecoded s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType s.g53.r1721_ndataBuffer_5F0_5Fctrl_5FfuOpType s.g53.r1718_ndataBuffer_5F0_5Fctrl_5Fsrc1Type s.g53.r1719_ndataBuffer_5F0_5Fctrl_5Fsrc2Type s.g54.r1733_ndataBuffer_5F0_5Fdata_5Fimm s.g53.r1724_ndataBuffer_5F0_5Fctrl_5FrfWen
theorem queue_addi0_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueAddi0 (step s i) := by
  change AddiDecoded (v26233 s i) (v28448 s i) (v28843 s i) (v28034 s i) (v28073 s i) (v29237 s i) (v28910 s i)
  simp [AddiDecoded, IsADDI, v26233, v28448, v28843, v28034, v28073, v29237, v28910, reset, v4051]
theorem queue_addi0_step (s : State) (i : Inputs) (old : QueueAddi0 s) :
    QueueAddi0 (step s i) := by
  change AddiDecoded (v26233 s i) (v28448 s i) (v28843 s i) (v28034 s i) (v28073 s i) (v29237 s i) (v28910 s i)
  change AddiDecoded s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g53.r1720_ndataBuffer_5F0_5Fctrl_5FfuType s.g53.r1721_ndataBuffer_5F0_5Fctrl_5FfuOpType s.g53.r1718_ndataBuffer_5F0_5Fctrl_5Fsrc1Type s.g53.r1719_ndataBuffer_5F0_5Fctrl_5Fsrc2Type s.g54.r1733_ndataBuffer_5F0_5Fdata_5Fimm s.g53.r1724_ndataBuffer_5F0_5Fctrl_5FrfWen at old
  have port0 := idu_addi_decoded_0 s i
  have port1 := idu_addi_decoded_1 s i
  simp only [v26233, v4051, v26232, v26231, v26230, v26208, v26203, v26213, v26212, v26211, v26229, v26228, v26221, v26216, v26227, v26226, v26225, v26224, v28448, v2687, v28447, v28446, v28445, v28075, v28074, v28257, v28256, v28255, v28444, v28443, v28259, v28258, v28442, v28441, v28440, v28439, v28843, v14452, v28842, v28841, v28840, v28450, v28449, v28839, v28838, v28645, v28644, v28837, v28034, v24, v28033, v28032, v28031, v27995, v27994, v28030, v28029, v28012, v28011, v28028, v28073, v28072, v28071, v28070, v28036, v28035, v28069, v28068, v28052, v28051, v28067, v29237, v29236, v29235, v29234, v29080, v29079, v29233, v29232, v29156, v29155, v29231, v28910, v28909, v28908, v28907, v28893, v28892, v28906, v28905, v28899, v28898, v28904]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [AddiDecoded, IsADDI]

def QueueAddi1 (s : State) : Prop :=
  AddiDecoded s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType s.g55.r1776_ndataBuffer_5F1_5Fctrl_5FfuOpType s.g55.r1773_ndataBuffer_5F1_5Fctrl_5Fsrc1Type s.g55.r1774_ndataBuffer_5F1_5Fctrl_5Fsrc2Type s.g55.r1788_ndataBuffer_5F1_5Fdata_5Fimm s.g55.r1779_ndataBuffer_5F1_5Fctrl_5FrfWen
theorem queue_addi1_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueAddi1 (step s i) := by
  change AddiDecoded (v29247 s i) (v29657 s i) (v29667 s i) (v29637 s i) (v29647 s i) (v29787 s i) (v29697 s i)
  simp [AddiDecoded, IsADDI, v29247, v29657, v29667, v29637, v29647, v29787, v29697, reset, v4051]
theorem queue_addi1_step (s : State) (i : Inputs) (old : QueueAddi1 s) :
    QueueAddi1 (step s i) := by
  change AddiDecoded (v29247 s i) (v29657 s i) (v29667 s i) (v29637 s i) (v29647 s i) (v29787 s i) (v29697 s i)
  change AddiDecoded s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g55.r1775_ndataBuffer_5F1_5Fctrl_5FfuType s.g55.r1776_ndataBuffer_5F1_5Fctrl_5FfuOpType s.g55.r1773_ndataBuffer_5F1_5Fctrl_5Fsrc1Type s.g55.r1774_ndataBuffer_5F1_5Fctrl_5Fsrc2Type s.g55.r1788_ndataBuffer_5F1_5Fdata_5Fimm s.g55.r1779_ndataBuffer_5F1_5Fctrl_5FrfWen at old
  have port0 := idu_addi_decoded_0 s i
  have port1 := idu_addi_decoded_1 s i
  simp only [v29247, v4051, v29246, v29245, v29244, v29239, v29238, v26213, v26212, v26211, v29243, v29242, v29241, v29240, v26227, v26226, v26225, v26224, v29657, v2687, v29656, v29655, v29654, v29649, v29648, v28257, v28256, v28255, v29653, v29652, v29651, v29650, v28442, v28441, v28440, v28439, v29667, v14452, v29666, v29665, v29664, v29659, v29658, v29663, v29662, v29661, v29660, v28837, v29637, v24, v29636, v29635, v29634, v29629, v29628, v29633, v29632, v29631, v29630, v28028, v29647, v29646, v29645, v29644, v29639, v29638, v29643, v29642, v29641, v29640, v28067, v29787, v29786, v29785, v29784, v29779, v29778, v29783, v29782, v29781, v29780, v29231, v29697, v29696, v29695, v29694, v29689, v29688, v29693, v29692, v29691, v29690, v28904]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [AddiDecoded, IsADDI]

def QueueAddi2 (s : State) : Prop :=
  AddiDecoded s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType s.g57.r1831_ndataBuffer_5F2_5Fctrl_5FfuOpType s.g57.r1828_ndataBuffer_5F2_5Fctrl_5Fsrc1Type s.g57.r1829_ndataBuffer_5F2_5Fctrl_5Fsrc2Type s.g57.r1843_ndataBuffer_5F2_5Fdata_5Fimm s.g57.r1834_ndataBuffer_5F2_5Fctrl_5FrfWen
theorem queue_addi2_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueAddi2 (step s i) := by
  change AddiDecoded (v29795 s i) (v30123 s i) (v30131 s i) (v30107 s i) (v30115 s i) (v30227 s i) (v30155 s i)
  simp [AddiDecoded, IsADDI, v29795, v30123, v30131, v30107, v30115, v30227, v30155, reset, v4051]
theorem queue_addi2_step (s : State) (i : Inputs) (old : QueueAddi2 s) :
    QueueAddi2 (step s i) := by
  change AddiDecoded (v29795 s i) (v30123 s i) (v30131 s i) (v30107 s i) (v30115 s i) (v30227 s i) (v30155 s i)
  change AddiDecoded s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g57.r1830_ndataBuffer_5F2_5Fctrl_5FfuType s.g57.r1831_ndataBuffer_5F2_5Fctrl_5FfuOpType s.g57.r1828_ndataBuffer_5F2_5Fctrl_5Fsrc1Type s.g57.r1829_ndataBuffer_5F2_5Fctrl_5Fsrc2Type s.g57.r1843_ndataBuffer_5F2_5Fdata_5Fimm s.g57.r1834_ndataBuffer_5F2_5Fctrl_5FrfWen at old
  have port0 := idu_addi_decoded_0 s i
  have port1 := idu_addi_decoded_1 s i
  simp only [v29795, v4051, v29794, v29793, v29792, v29788, v9721, v26213, v26212, v26211, v29791, v29790, v29789, v26227, v26226, v26225, v26224, v30123, v2687, v30122, v30121, v30120, v30116, v28257, v28256, v28255, v30119, v30118, v30117, v28442, v28441, v28440, v28439, v30131, v14452, v30130, v30129, v30128, v30124, v30127, v30126, v30125, v28837, v30107, v24, v30106, v30105, v30104, v30100, v30103, v30102, v30101, v28028, v30115, v30114, v30113, v30112, v30108, v30111, v30110, v30109, v28067, v30227, v30226, v30225, v30224, v30220, v30223, v30222, v30221, v29231, v30155, v30154, v30153, v30152, v30148, v30151, v30150, v30149, v28904]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [AddiDecoded, IsADDI]

def QueueAddi3 (s : State) : Prop :=
  AddiDecoded s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType s.g58.r1886_ndataBuffer_5F3_5Fctrl_5FfuOpType s.g58.r1883_ndataBuffer_5F3_5Fctrl_5Fsrc1Type s.g58.r1884_ndataBuffer_5F3_5Fctrl_5Fsrc2Type s.g59.r1898_ndataBuffer_5F3_5Fdata_5Fimm s.g59.r1889_ndataBuffer_5F3_5Fctrl_5FrfWen
theorem queue_addi3_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueAddi3 (step s i) := by
  change AddiDecoded (v30235 s i) (v30563 s i) (v30571 s i) (v30547 s i) (v30555 s i) (v30667 s i) (v30595 s i)
  simp [AddiDecoded, IsADDI, v30235, v30563, v30571, v30547, v30555, v30667, v30595, reset, v4051]
theorem queue_addi3_step (s : State) (i : Inputs) (old : QueueAddi3 s) :
    QueueAddi3 (step s i) := by
  change AddiDecoded (v30235 s i) (v30563 s i) (v30571 s i) (v30547 s i) (v30555 s i) (v30667 s i) (v30595 s i)
  change AddiDecoded s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g58.r1885_ndataBuffer_5F3_5Fctrl_5FfuType s.g58.r1886_ndataBuffer_5F3_5Fctrl_5FfuOpType s.g58.r1883_ndataBuffer_5F3_5Fctrl_5Fsrc1Type s.g58.r1884_ndataBuffer_5F3_5Fctrl_5Fsrc2Type s.g59.r1898_ndataBuffer_5F3_5Fdata_5Fimm s.g59.r1889_ndataBuffer_5F3_5Fctrl_5FrfWen at old
  have port0 := idu_addi_decoded_0 s i
  have port1 := idu_addi_decoded_1 s i
  simp only [v30235, v4051, v30234, v30233, v30232, v30228, v2750, v26213, v26212, v26211, v30231, v30230, v30229, v26227, v26226, v26225, v26224, v30563, v2687, v30562, v30561, v30560, v30556, v28257, v28256, v28255, v30559, v30558, v30557, v28442, v28441, v28440, v28439, v30571, v14452, v30570, v30569, v30568, v30564, v30567, v30566, v30565, v28837, v30547, v24, v30546, v30545, v30544, v30540, v30543, v30542, v30541, v28028, v30555, v30554, v30553, v30552, v30548, v30551, v30550, v30549, v28067, v30667, v30666, v30665, v30664, v30660, v30663, v30662, v30661, v29231, v30595, v30594, v30593, v30592, v30588, v30591, v30590, v30589, v28904]
  repeat' first | assumption | (split <;> try simp_all only [↓reduceIte])
  all_goals simp_all [AddiDecoded, IsADDI]

def QueueAddiDecoded (s : State) : Prop :=
  QueueAddi0 s ∧ QueueAddi1 s ∧ QueueAddi2 s ∧ QueueAddi3 s
theorem queue_selected_addi (s : State) (i : Inputs) (queue : QueueAddiDecoded s) :
    AddiDecoded (v24297 s i) (v24912 s i) (v24927 s i) (v24882 s i) (v24897 s i) (v25326 s i) (v24946 s i) := by
  rcases queue with ⟨h0, h1, h2, h3⟩
  have bound := s.g59.r1900_nringBufferTail.isLt
  have cases : s.g59.r1900_nringBufferTail.toNat = 0 ∨ s.g59.r1900_nringBufferTail.toNat = 1 ∨ s.g59.r1900_nringBufferTail.toNat = 2 ∨ s.g59.r1900_nringBufferTail.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : s.g59.r1900_nringBufferTail = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v24927, v24926, v24925, v24924, v24914, v24923, v24915, v24922, v24917, v24916, v24921, v24920, v24919, v24918, v24882, v24881, v24880, v24879, v24869, v24878, v24870, v24877, v24872, v24871, v24876, v24875, v24874, v24873, v24897, v24896, v24895, v24894, v24884, v24893, v24885, v24892, v24887, v24886, v24891, v24890, v24889, v24888, v25326, v25220, v25219, v25218, v25208, v25217, v25209, v25216, v25211, v25210, v25215, v25214, v25213, v25212, v24946, v24945, v24944, v24943, v24933, v24942, v24934, v24941, v24936, v24935, v24940, v24939, v24938, v24937, eq, QueueAddi0] using h0
  · have eq : s.g59.r1900_nringBufferTail = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v24927, v24926, v24925, v24924, v24914, v24923, v24915, v24922, v24917, v24916, v24921, v24920, v24919, v24918, v24882, v24881, v24880, v24879, v24869, v24878, v24870, v24877, v24872, v24871, v24876, v24875, v24874, v24873, v24897, v24896, v24895, v24894, v24884, v24893, v24885, v24892, v24887, v24886, v24891, v24890, v24889, v24888, v25326, v25220, v25219, v25218, v25208, v25217, v25209, v25216, v25211, v25210, v25215, v25214, v25213, v25212, v24946, v24945, v24944, v24943, v24933, v24942, v24934, v24941, v24936, v24935, v24940, v24939, v24938, v24937, eq, QueueAddi1] using h1
  · have eq : s.g59.r1900_nringBufferTail = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v24927, v24926, v24925, v24924, v24914, v24923, v24915, v24922, v24917, v24916, v24921, v24920, v24919, v24918, v24882, v24881, v24880, v24879, v24869, v24878, v24870, v24877, v24872, v24871, v24876, v24875, v24874, v24873, v24897, v24896, v24895, v24894, v24884, v24893, v24885, v24892, v24887, v24886, v24891, v24890, v24889, v24888, v25326, v25220, v25219, v25218, v25208, v25217, v25209, v25216, v25211, v25210, v25215, v25214, v25213, v25212, v24946, v24945, v24944, v24943, v24933, v24942, v24934, v24941, v24936, v24935, v24940, v24939, v24938, v24937, eq, QueueAddi2] using h2
  · have eq : s.g59.r1900_nringBufferTail = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24912, v24911, v24910, v24909, v24899, v24908, v24900, v24907, v24902, v24901, v24906, v24905, v24904, v24903, v24927, v24926, v24925, v24924, v24914, v24923, v24915, v24922, v24917, v24916, v24921, v24920, v24919, v24918, v24882, v24881, v24880, v24879, v24869, v24878, v24870, v24877, v24872, v24871, v24876, v24875, v24874, v24873, v24897, v24896, v24895, v24894, v24884, v24893, v24885, v24892, v24887, v24886, v24891, v24890, v24889, v24888, v25326, v25220, v25219, v25218, v25208, v25217, v25209, v25216, v25211, v25210, v25215, v25214, v25213, v25212, v24946, v24945, v24944, v24943, v24933, v24942, v24934, v24941, v24936, v24935, v24940, v24939, v24938, v24937, eq, QueueAddi3] using h3
def ExecuteAddiDecoded (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 → AddiDecoded s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr s.g48.r1553_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FfuType s.g48.r1554_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FfuOpType s.g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type s.g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type s.g48.r1566_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fimm s.g48.r1557_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfWen
theorem execute_addi_step (s : State) (i : Inputs)
    (queue : QueueAddiDecoded s) (old : ExecuteAddiDecoded s) :
    ExecuteAddiDecoded (step s i) := by
  intro valid
  change AddiDecoded (v24298 s i) (v24913 s i) (v24928 s i) (v24883 s i) (v24898 s i) (v25327 s i) (v24947 s i)
  by_cases fire : v24283 s i = 1
  · simpa only [v24298, v24913, v24928, v24883, v24898, v25327, v24947, fire, ↓reduceIte] using queue_selected_addi s i queue
  · simp only [v24298, v24913, v24928, v24883, v24898, v25327, v24947, fire, ↓reduceIte]
    exact old (execute_valid_backward s i i valid fire)
def AddiDecodeState (s : State) : Prop := QueueAddiDecoded s ∧ ExecuteAddiDecoded s
theorem addi_decode_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    AddiDecodeState (step s i) := by
  constructor
  · exact ⟨queue_addi0_reset s i reset, queue_addi1_reset s i reset, queue_addi2_reset s i reset, queue_addi3_reset s i reset⟩
  · intro valid
    have zero := execute_valid_reset s i i reset
    change v6 (step s i) i = 1 at valid
    rw [zero] at valid
    contradiction
theorem addi_decode_step (s : State) (i : Inputs) (old : AddiDecodeState s) :
    AddiDecodeState (step s i) := by
  rcases old with ⟨queue, exu⟩
  refine ⟨?_, execute_addi_step s i queue exu⟩
  rcases queue with ⟨h0, h1, h2, h3⟩
  exact ⟨queue_addi0_step s i h0, queue_addi1_step s i h1, queue_addi2_step s i h2, queue_addi3_step s i h3⟩
theorem addi_decode_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    AddiDecodeState (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact addi_decode_reset initial (inputs 0) reset
  | succ t ih => exact addi_decode_step _ _ ih
#print axioms addi_decode_run
end NutShellProofs
