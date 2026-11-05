import Proofs.NonAtomicPipeline
namespace NutShellProofs
open nNutCore

/-- A relation between instruction bits and their associated PC in every queue slot. -/
def QueueInstructionPC (relation : BitVec 64 → BitVec 39 → Prop) (s : State) : Prop :=
  relation s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g52.r1680_ndataBuffer_5F0_5Fcf_5Fpc ∧
  relation s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g54.r1735_ndataBuffer_5F1_5Fcf_5Fpc ∧
  relation s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g55.r1790_ndataBuffer_5F2_5Fcf_5Fpc ∧
  relation s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g57.r1845_ndataBuffer_5F3_5Fcf_5Fpc

/-- The two independent generated muxes select the same slot, including tail zero. -/
theorem queue_selected_instruction_pc (relation : BitVec 64 → BitVec 39 → Prop)
    (s : State) (i : Inputs) (queue : QueueInstructionPC relation s) :
    relation (v24297 s i) (v24312 s i) := by
  rcases queue with ⟨h0, h1, h2, h3⟩
  have bound := s.g59.r1900_nringBufferTail.isLt
  have cases : s.g59.r1900_nringBufferTail.toNat = 0 ∨
      s.g59.r1900_nringBufferTail.toNat = 1 ∨
      s.g59.r1900_nringBufferTail.toNat = 2 ∨
      s.g59.r1900_nringBufferTail.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : s.g59.r1900_nringBufferTail = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24284, v24285, v24286, v24287, v24288, v24289, v24290, v24291, v24292, v24293, v24294, v24295, v24296, v24297, v24299, v24300, v24301, v24302, v24303, v24304, v24305, v24306, v24307, v24308, v24309, v24310, v24311, v24312, v2750, v9721, v110, eq] using h0
  · have eq : s.g59.r1900_nringBufferTail = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24284, v24285, v24286, v24287, v24288, v24289, v24290, v24291, v24292, v24293, v24294, v24295, v24296, v24297, v24299, v24300, v24301, v24302, v24303, v24304, v24305, v24306, v24307, v24308, v24309, v24310, v24311, v24312, v2750, v9721, v110, eq] using h1
  · have eq : s.g59.r1900_nringBufferTail = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24284, v24285, v24286, v24287, v24288, v24289, v24290, v24291, v24292, v24293, v24294, v24295, v24296, v24297, v24299, v24300, v24301, v24302, v24303, v24304, v24305, v24306, v24307, v24308, v24309, v24310, v24311, v24312, v2750, v9721, v110, eq] using h2
  · have eq : s.g59.r1900_nringBufferTail = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24284, v24285, v24286, v24287, v24288, v24289, v24290, v24291, v24292, v24293, v24294, v24295, v24296, v24297, v24299, v24300, v24301, v24302, v24303, v24304, v24305, v24306, v24307, v24308, v24309, v24310, v24311, v24312, v2750, v9721, v110, eq] using h3

def EXUInstructionPC (relation : BitVec 64 → BitVec 39 → Prop) (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 →
    relation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr
      s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc

/-- Capture or stall preserves any paired relation, rather than just separate facts. -/
theorem exu_instruction_pc_step (relation : BitVec 64 → BitVec 39 → Prop)
    (s : State) (i : Inputs) (queue : QueueInstructionPC relation s)
    (old : EXUInstructionPC relation s) : EXUInstructionPC relation (step s i) := by
  intro valid
  change relation (v24298 s i) (v24313 s i)
  by_cases fire : v24283 s i = 1
  · rw [v24298, v24313, if_pos fire, if_pos fire]
    exact queue_selected_instruction_pc relation s i queue
  · rw [v24298, v24313, if_neg fire, if_neg fire]
    exact old (execute_valid_backward s i i valid fire)

#print axioms queue_selected_instruction_pc
#print axioms exu_instruction_pc_step


theorem queue_instruction_pc_step_0 (relation : BitVec 64 → BitVec 39 → Prop)
    (s : State) (i : Inputs) (zero : relation 0 0)
    (old : relation s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g52.r1680_ndataBuffer_5F0_5Fcf_5Fpc)
    (source : v9827 s i = 1 → relation s.g38.r1242_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Finstr
      s.g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc) :
    relation (step s i).g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr
      (step s i).g52.r1680_ndataBuffer_5F0_5Fcf_5Fpc := by
  change relation (v26233 s i) (v26254 s i)
  simp only [v24, v4051, v8200, v9721, v26189, v26190, v26191, v26192, v26193, v26194, v26195, v26196, v26197, v26198, v26199, v26200, v26201, v26202, v26203, v26204, v26205, v26206, v26207, v26208, v26209, v26210, v26211, v26212, v26213, v26214, v26215, v26216, v26217, v26218, v26219, v26220, v26221, v26222, v26223, v26224, v26225, v26226, v26227, v26228, v26229, v26230, v26231, v26232, v26233, v26234, v26235, v26236, v26237, v26238, v26239, v26240, v26241, v26242, v26243, v26244, v26245, v26246, v26247, v26248, v26249, v26250, v26251, v26252, v26253, v26254]
  rcases BitVec.eq_zero_or_eq_one (v9827 s i) with idle | valid
  · simp [idle] <;> repeat' first | assumption | split
  · have paired := source valid
    simp [valid] <;> repeat' first | assumption | split


theorem queue_instruction_pc_step_1 (relation : BitVec 64 → BitVec 39 → Prop)
    (s : State) (i : Inputs) (zero : relation 0 0)
    (old : relation s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g54.r1735_ndataBuffer_5F1_5Fcf_5Fpc)
    (source : v9827 s i = 1 → relation s.g38.r1242_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Finstr
      s.g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc) :
    relation (step s i).g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr
      (step s i).g54.r1735_ndataBuffer_5F1_5Fcf_5Fpc := by
  change relation (v29247 s i) (v29257 s i)
  simp only [v24, v4051, v8200, v9721, v26189, v26190, v26191, v26192, v26193, v26194, v26195, v26196, v26197, v26198, v26199, v26200, v26201, v26202, v26204, v26205, v26206, v26207, v26209, v26210, v26211, v26212, v26213, v26214, v26215, v26217, v26218, v26219, v26220, v26222, v26223, v26224, v26225, v26226, v26227, v26236, v26237, v26238, v26239, v26240, v26243, v26244, v26245, v26246, v26247, v26248, v29238, v29239, v29240, v29241, v29242, v29243, v29244, v29245, v29246, v29247, v29248, v29249, v29250, v29251, v29252, v29253, v29254, v29255, v29256, v29257]
  rcases BitVec.eq_zero_or_eq_one (v9827 s i) with idle | valid
  · simp [idle] <;> repeat' first | assumption | split
  · have paired := source valid
    simp [valid] <;> repeat' first | assumption | split


theorem queue_instruction_pc_step_2 (relation : BitVec 64 → BitVec 39 → Prop)
    (s : State) (i : Inputs) (zero : relation 0 0)
    (old : relation s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g55.r1790_ndataBuffer_5F2_5Fcf_5Fpc)
    (source : v9827 s i = 1 → relation s.g38.r1242_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Finstr
      s.g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc) :
    relation (step s i).g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr
      (step s i).g55.r1790_ndataBuffer_5F2_5Fcf_5Fpc := by
  change relation (v29795 s i) (v29803 s i)
  simp only [v24, v4051, v8200, v9721, v26189, v26190, v26191, v26192, v26193, v26194, v26195, v26196, v26197, v26198, v26199, v26200, v26201, v26202, v26204, v26205, v26206, v26207, v26209, v26210, v26211, v26212, v26213, v26214, v26215, v26217, v26218, v26219, v26220, v26222, v26223, v26224, v26225, v26226, v26227, v26236, v26237, v26238, v26239, v26240, v26243, v26244, v26245, v26246, v26247, v26248, v29788, v29789, v29790, v29791, v29792, v29793, v29794, v29795, v29796, v29797, v29798, v29799, v29800, v29801, v29802, v29803]
  rcases BitVec.eq_zero_or_eq_one (v9827 s i) with idle | valid
  · simp [idle] <;> repeat' first | assumption | split
  · have paired := source valid
    simp [valid] <;> repeat' first | assumption | split


theorem queue_instruction_pc_step_3 (relation : BitVec 64 → BitVec 39 → Prop)
    (s : State) (i : Inputs) (zero : relation 0 0)
    (old : relation s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g57.r1845_ndataBuffer_5F3_5Fcf_5Fpc)
    (source : v9827 s i = 1 → relation s.g38.r1242_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Finstr
      s.g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc) :
    relation (step s i).g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr
      (step s i).g57.r1845_ndataBuffer_5F3_5Fcf_5Fpc := by
  change relation (v30235 s i) (v30243 s i)
  simp only [v24, v2750, v4051, v8200, v9721, v26189, v26190, v26191, v26192, v26193, v26194, v26195, v26196, v26197, v26198, v26199, v26200, v26201, v26202, v26204, v26205, v26206, v26207, v26209, v26210, v26211, v26212, v26213, v26214, v26215, v26217, v26218, v26219, v26220, v26222, v26223, v26224, v26225, v26226, v26227, v26236, v26237, v26238, v26239, v26240, v26243, v26244, v26245, v26246, v26247, v26248, v30228, v30229, v30230, v30231, v30232, v30233, v30234, v30235, v30236, v30237, v30238, v30239, v30240, v30241, v30242, v30243]
  rcases BitVec.eq_zero_or_eq_one (v9827 s i) with idle | valid
  · simp [idle] <;> repeat' first | assumption | split
  · have paired := source valid
    simp [valid] <;> repeat' first | assumption | split


theorem queue_instruction_pc_step (relation : BitVec 64 → BitVec 39 → Prop)
    (s : State) (i : Inputs) (zero : relation 0 0)
    (old : QueueInstructionPC relation s)
    (source : v9827 s i = 1 →
      relation s.g38.r1242_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Finstr
        s.g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc) :
    QueueInstructionPC relation (step s i) := by
  rcases old with ⟨h0, h1, h2, h3⟩
  exact ⟨queue_instruction_pc_step_0 relation s i zero h0 source,
    queue_instruction_pc_step_1 relation s i zero h1 source,
    queue_instruction_pc_step_2 relation s i zero h2 source,
    queue_instruction_pc_step_3 relation s i zero h3 source⟩

#print axioms queue_instruction_pc_step
end NutShellProofs
