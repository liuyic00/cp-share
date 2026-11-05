import Proofs.IDUNonAtomic
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem idu_non_atomic_lsu_decode_0 (s : State) (i : Inputs)
    (nonAtomic : NonAtomicInstruction (v26210 s i)) (lsu : v28254 s i = 1) :
    BitVec.extractLsb' 5 1 (v28643 s i) = 0 := by
  have hv26729 : v26729 s i = 0 := by
    have miss : v26726 s i ≠ v26210 s i &&& v26727 s i := by
      intro matched
      have opcode := opcode_of_mask (v26210 s i) (v26727 s i) (v26726 s i) (by unfold v26727; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v26726 s i) = 47 := by unfold v26726; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv26734 : v26734 s i = 0 := by
    have miss : v26731 s i ≠ v26210 s i &&& v26732 s i := by
      intro matched
      have opcode := opcode_of_mask (v26210 s i) (v26732 s i) (v26731 s i) (by unfold v26732; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v26731 s i) = 47 := by unfold v26731; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv26739 : v26739 s i = 0 := by
    have miss : v26736 s i ≠ v26210 s i &&& v26737 s i := by
      intro matched
      have opcode := opcode_of_mask (v26210 s i) (v26737 s i) (v26736 s i) (by unfold v26737; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v26736 s i) = 47 := by unfold v26736; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv26743 : v26743 s i = 0 := by
    have miss : v26740 s i ≠ v26210 s i &&& v26741 s i := by
      intro matched
      have opcode := opcode_of_mask (v26210 s i) (v26741 s i) (v26740 s i) (by unfold v26741; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v26740 s i) = 47 := by unfold v26740; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv26747 : v26747 s i = 0 := by
    have miss : v26744 s i ≠ v26210 s i &&& v26745 s i := by
      intro matched
      have opcode := opcode_of_mask (v26210 s i) (v26745 s i) (v26744 s i) (by unfold v26745; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v26744 s i) = 47 := by unfold v26744; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv26751 : v26751 s i = 0 := by
    have miss : v26748 s i ≠ v26210 s i &&& v26749 s i := by
      intro matched
      have opcode := opcode_of_mask (v26210 s i) (v26749 s i) (v26748 s i) (by unfold v26749; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v26748 s i) = 47 := by unfold v26748; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv26755 : v26755 s i = 0 := by
    have miss : v26752 s i ≠ v26210 s i &&& v26753 s i := by
      intro matched
      have opcode := opcode_of_mask (v26210 s i) (v26753 s i) (v26752 s i) (by unfold v26753; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v26752 s i) = 47 := by unfold v26752; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv26759 : v26759 s i = 0 := by
    have miss : v26756 s i ≠ v26210 s i &&& v26757 s i := by
      intro matched
      have opcode := opcode_of_mask (v26210 s i) (v26757 s i) (v26756 s i) (by unfold v26757; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v26756 s i) = 47 := by unfold v26756; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv26763 : v26763 s i = 0 := by
    have miss : v26760 s i ≠ v26210 s i &&& v26761 s i := by
      intro matched
      have opcode := opcode_of_mask (v26210 s i) (v26761 s i) (v26760 s i) (by unfold v26761; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v26760 s i) = 47 := by unfold v26760; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv26767 : v26767 s i = 0 := by
    have miss : v26764 s i ≠ v26210 s i &&& v26765 s i := by
      intro matched
      have opcode := opcode_of_mask (v26210 s i) (v26765 s i) (v26764 s i) (by unfold v26765; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v26764 s i) = 47 := by unfold v26764; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv26771 : v26771 s i = 0 := by
    have miss : v26768 s i ≠ v26210 s i &&& v26769 s i := by
      intro matched
      have opcode := opcode_of_mask (v26210 s i) (v26769 s i) (v26768 s i) (by unfold v26769; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v26768 s i) = 47 := by unfold v26768; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv26775 : v26775 s i = 0 := by
    have miss : v26772 s i ≠ v26210 s i &&& v26773 s i := by
      intro matched
      have opcode := opcode_of_mask (v26210 s i) (v26773 s i) (v26772 s i) (by unfold v26773; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v26772 s i) = 47 := by unfold v26772; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv26779 : v26779 s i = 0 := by
    have miss : v26776 s i ≠ v26210 s i &&& v26777 s i := by
      intro matched
      have opcode := opcode_of_mask (v26210 s i) (v26777 s i) (v26776 s i) (by unfold v26777; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v26776 s i) = 47 := by unfold v26776; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have tail : v28165 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by simp [v28165]
  have hv28166 : v28166 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by
    by_cases selected : v26807 s i = 1
    · simp only [v28166, selected, ↓reduceIte]
      simp [v4]
    · simpa only [v28166, selected, ↓reduceIte] using tail
  have hv28167 : v28167 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by
    by_cases selected : v26803 s i = 1
    · simp only [v28167, selected, ↓reduceIte]
      simp [v28164]
    · simpa only [v28167, selected, ↓reduceIte] using hv28166
  have hv28168 : v28168 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by
    by_cases selected : v26799 s i = 1
    · simp only [v28168, selected, ↓reduceIte]
      simp [v28163]
    · simpa only [v28168, selected, ↓reduceIte] using hv28167
  have hv28169 : v28169 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by
    by_cases selected : v26795 s i = 1
    · simp only [v28169, selected, ↓reduceIte]
      simp [v28162]
    · simpa only [v28169, selected, ↓reduceIte] using hv28168
  have hv28170 : v28170 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by
    by_cases selected : v26791 s i = 1
    · simp only [v28170, selected, ↓reduceIte]
      simp [v28161]
    · simpa only [v28170, selected, ↓reduceIte] using hv28169
  have hv28171 : v28171 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by
    by_cases selected : v26787 s i = 1
    · simp only [v28171, selected, ↓reduceIte]
      simp [v28160]
    · simpa only [v28171, selected, ↓reduceIte] using hv28170
  have hv28172 : v28172 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by
    by_cases selected : v26783 s i = 1
    · simp only [v28172, selected, ↓reduceIte]
      simp [v28159]
    · simpa only [v28172, selected, ↓reduceIte] using hv28171
  have hv28173 : v28173 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by
    simpa only [v28173, hv26779, ↓reduceIte] using hv28172
  have hv28174 : v28174 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by
    simpa only [v28174, hv26775, ↓reduceIte] using hv28173
  have hv28175 : v28175 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by
    simpa only [v28175, hv26771, ↓reduceIte] using hv28174
  have hv28176 : v28176 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by
    simpa only [v28176, hv26767, ↓reduceIte] using hv28175
  have hv28177 : v28177 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by
    simpa only [v28177, hv26763, ↓reduceIte] using hv28176
  have hv28178 : v28178 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by
    simpa only [v28178, hv26759, ↓reduceIte] using hv28177
  have hv28179 : v28179 s i = 1 → BitVec.extractLsb' 5 1 (v28540 s i) = 0 := by
    simpa only [v28179, hv26755, ↓reduceIte] using hv28178
  have hv28180 : v28180 s i = 1 → BitVec.extractLsb' 5 1 (v28541 s i) = 0 := by
    simpa only [v28180, v28541, hv26751, ↓reduceIte] using hv28179
  have hv28181 : v28181 s i = 1 → BitVec.extractLsb' 5 1 (v28542 s i) = 0 := by
    simpa only [v28181, v28542, hv26747, ↓reduceIte] using hv28180
  have hv28182 : v28182 s i = 1 → BitVec.extractLsb' 5 1 (v28543 s i) = 0 := by
    simpa only [v28182, v28543, hv26743, ↓reduceIte] using hv28181
  have hv28183 : v28183 s i = 1 → BitVec.extractLsb' 5 1 (v28544 s i) = 0 := by
    simpa only [v28183, v28544, hv26739, ↓reduceIte] using hv28182
  have hv28184 : v28184 s i = 1 → BitVec.extractLsb' 5 1 (v28545 s i) = 0 := by
    simpa only [v28184, v28545, hv26734, ↓reduceIte] using hv28183
  have hv28185 : v28185 s i = 1 → BitVec.extractLsb' 5 1 (v28546 s i) = 0 := by
    simpa only [v28185, v28546, hv26729, ↓reduceIte] using hv28184
  have hv28186 : v28186 s i = 1 → BitVec.extractLsb' 5 1 (v28547 s i) = 0 := by
    by_cases selected : v26724 s i = 1
    · simp only [v28186, v28547, selected, ↓reduceIte]
      simp [v28145]
    · simpa only [v28186, v28547, selected, ↓reduceIte] using hv28185
  have hv28187 : v28187 s i = 1 → BitVec.extractLsb' 5 1 (v28548 s i) = 0 := by
    by_cases selected : v26719 s i = 1
    · simp only [v28187, v28548, selected, ↓reduceIte]
      simp [v4]
    · simpa only [v28187, v28548, selected, ↓reduceIte] using hv28186
  have hv28188 : v28188 s i = 1 → BitVec.extractLsb' 5 1 (v28549 s i) = 0 := by
    by_cases selected : v26714 s i = 1
    · simp only [v28188, v28549, selected, ↓reduceIte]
      simp [v28144]
    · simpa only [v28188, v28549, selected, ↓reduceIte] using hv28187
  have hv28189 : v28189 s i = 1 → BitVec.extractLsb' 5 1 (v28550 s i) = 0 := by
    by_cases selected : v26709 s i = 1
    · simp only [v28189, v28550, selected, ↓reduceIte]
      simp [v28143]
    · simpa only [v28189, v28550, selected, ↓reduceIte] using hv28188
  have hv28190 : v28190 s i = 1 → BitVec.extractLsb' 5 1 (v28551 s i) = 0 := by
    by_cases selected : v26704 s i = 1
    · simp only [v28190, v28551, selected, ↓reduceIte]
      simp [v28142]
    · simpa only [v28190, v28551, selected, ↓reduceIte] using hv28189
  have hv28191 : v28191 s i = 1 → BitVec.extractLsb' 5 1 (v28552 s i) = 0 := by
    by_cases selected : v26699 s i = 1
    · simp only [v28191, v28552, selected, ↓reduceIte]
      simp [v28141]
    · simpa only [v28191, v28552, selected, ↓reduceIte] using hv28190
  have hv28192 : v28192 s i = 1 → BitVec.extractLsb' 5 1 (v28553 s i) = 0 := by
    by_cases selected : v26694 s i = 1
    · simp only [v28192, v28553, selected, ↓reduceIte]
      simp [v28140]
    · simpa only [v28192, v28553, selected, ↓reduceIte] using hv28191
  have hv28193 : v28193 s i = 1 → BitVec.extractLsb' 5 1 (v28554 s i) = 0 := by
    by_cases selected : v26689 s i = 1
    · simp only [v28193, v28554, selected, ↓reduceIte]
      simp [v28139]
    · simpa only [v28193, v28554, selected, ↓reduceIte] using hv28192
  have hv28194 : v28194 s i = 1 → BitVec.extractLsb' 5 1 (v28555 s i) = 0 := by
    by_cases selected : v26684 s i = 1
    · simp only [v28194, v28555, selected, ↓reduceIte]
      simp [v28138]
    · simpa only [v28194, v28555, selected, ↓reduceIte] using hv28193
  have hv28195 : v28195 s i = 1 → BitVec.extractLsb' 5 1 (v28556 s i) = 0 := by
    by_cases selected : v26679 s i = 1
    · simp only [v28195, v28556, selected, ↓reduceIte]
      simp [v28137]
    · simpa only [v28195, v28556, selected, ↓reduceIte] using hv28194
  have hv28196 : v28196 s i = 1 → BitVec.extractLsb' 5 1 (v28557 s i) = 0 := by
    by_cases selected : v26674 s i = 1
    · simp only [v28196, v28557, selected, ↓reduceIte]
      simp [v28136]
    · simpa only [v28196, v28557, selected, ↓reduceIte] using hv28195
  have hv28197 : v28197 s i = 1 → BitVec.extractLsb' 5 1 (v28558 s i) = 0 := by
    by_cases selected : v26669 s i = 1
    · simp only [v28197, v28558, selected, ↓reduceIte]
      simp [v28135]
    · simpa only [v28197, v28558, selected, ↓reduceIte] using hv28196
  have hv28198 : v28198 s i = 1 → BitVec.extractLsb' 5 1 (v28559 s i) = 0 := by
    by_cases selected : v26664 s i = 1
    · simp only [v28198, v28559, selected, ↓reduceIte]
      simp [v28134]
    · simpa only [v28198, v28559, selected, ↓reduceIte] using hv28197
  have hv28199 : v28199 s i = 1 → BitVec.extractLsb' 5 1 (v28560 s i) = 0 := by
    by_cases selected : v26659 s i = 1
    · simp only [v28199, v28560, selected, ↓reduceIte]
      simp [v28133]
    · simpa only [v28199, v28560, selected, ↓reduceIte] using hv28198
  have hv28200 : v28200 s i = 1 → BitVec.extractLsb' 5 1 (v28561 s i) = 0 := by
    by_cases selected : v26654 s i = 1
    · simp only [v28200, v28561, selected, ↓reduceIte]
      simp [v28132]
    · simpa only [v28200, v28561, selected, ↓reduceIte] using hv28199
  have hv28201 : v28201 s i = 1 → BitVec.extractLsb' 5 1 (v28562 s i) = 0 := by
    by_cases selected : v26649 s i = 1
    · simp only [v28201, v28562, selected, ↓reduceIte]
      simp [v28131]
    · simpa only [v28201, v28562, selected, ↓reduceIte] using hv28200
  have hv28202 : v28202 s i = 1 → BitVec.extractLsb' 5 1 (v28563 s i) = 0 := by
    by_cases selected : v26644 s i = 1
    · simp only [v28202, v28563, selected, ↓reduceIte]
      simp [v28130]
    · simpa only [v28202, v28563, selected, ↓reduceIte] using hv28201
  have hv28203 : v28203 s i = 1 → BitVec.extractLsb' 5 1 (v28564 s i) = 0 := by
    by_cases selected : v26639 s i = 1
    · simp only [v28203, v28564, selected, ↓reduceIte]
      simp [v28129]
    · simpa only [v28203, v28564, selected, ↓reduceIte] using hv28202
  have hv28204 : v28204 s i = 1 → BitVec.extractLsb' 5 1 (v28565 s i) = 0 := by
    by_cases selected : v26634 s i = 1
    · simp only [v28204, v28565, selected, ↓reduceIte]
      simp [v28128]
    · simpa only [v28204, v28565, selected, ↓reduceIte] using hv28203
  have hv28205 : v28205 s i = 1 → BitVec.extractLsb' 5 1 (v28566 s i) = 0 := by
    by_cases selected : v26629 s i = 1
    · simp only [v28205, v28566, selected, ↓reduceIte]
      intro _
      unfold v28497
      decide
    · simpa only [v28205, v28566, selected, ↓reduceIte] using hv28204
  have hv28206 : v28206 s i = 1 → BitVec.extractLsb' 5 1 (v28567 s i) = 0 := by
    by_cases selected : v26624 s i = 1
    · simp only [v28206, v28567, selected, ↓reduceIte]
      intro _
      unfold v28496
      decide
    · simpa only [v28206, v28567, selected, ↓reduceIte] using hv28205
  have hv28207 : v28207 s i = 1 → BitVec.extractLsb' 5 1 (v28568 s i) = 0 := by
    by_cases selected : v26619 s i = 1
    · simp only [v28207, v28568, selected, ↓reduceIte]
      intro _
      unfold v28495
      decide
    · simpa only [v28207, v28568, selected, ↓reduceIte] using hv28206
  have hv28208 : v28208 s i = 1 → BitVec.extractLsb' 5 1 (v28569 s i) = 0 := by
    by_cases selected : v26614 s i = 1
    · simp only [v28208, v28569, selected, ↓reduceIte]
      simp [v28124]
    · simpa only [v28208, v28569, selected, ↓reduceIte] using hv28207
  have hv28209 : v28209 s i = 1 → BitVec.extractLsb' 5 1 (v28570 s i) = 0 := by
    by_cases selected : v26609 s i = 1
    · simp only [v28209, v28570, selected, ↓reduceIte]
      simp [v28123]
    · simpa only [v28209, v28570, selected, ↓reduceIte] using hv28208
  have hv28210 : v28210 s i = 1 → BitVec.extractLsb' 5 1 (v28571 s i) = 0 := by
    by_cases selected : v26604 s i = 1
    · simp only [v28210, v28571, selected, ↓reduceIte]
      simp [v28122]
    · simpa only [v28210, v28571, selected, ↓reduceIte] using hv28209
  have hv28211 : v28211 s i = 1 → BitVec.extractLsb' 5 1 (v28572 s i) = 0 := by
    by_cases selected : v26599 s i = 1
    · simp only [v28211, v28572, selected, ↓reduceIte]
      simp [v28121]
    · simpa only [v28211, v28572, selected, ↓reduceIte] using hv28210
  have hv28212 : v28212 s i = 1 → BitVec.extractLsb' 5 1 (v28573 s i) = 0 := by
    by_cases selected : v26594 s i = 1
    · simp only [v28212, v28573, selected, ↓reduceIte]
      simp [v28120]
    · simpa only [v28212, v28573, selected, ↓reduceIte] using hv28211
  have hv28213 : v28213 s i = 1 → BitVec.extractLsb' 5 1 (v28574 s i) = 0 := by
    by_cases selected : v26589 s i = 1
    · simp only [v28213, v28574, selected, ↓reduceIte]
      simp [v28119]
    · simpa only [v28213, v28574, selected, ↓reduceIte] using hv28212
  have hv28214 : v28214 s i = 1 → BitVec.extractLsb' 5 1 (v28575 s i) = 0 := by
    by_cases selected : v26584 s i = 1
    · simp only [v28214, v28575, selected, ↓reduceIte]
      simp [v28118]
    · simpa only [v28214, v28575, selected, ↓reduceIte] using hv28213
  have hv28215 : v28215 s i = 1 → BitVec.extractLsb' 5 1 (v28576 s i) = 0 := by
    by_cases selected : v26579 s i = 1
    · simp only [v28215, v28576, selected, ↓reduceIte]
      simp [v28117]
    · simpa only [v28215, v28576, selected, ↓reduceIte] using hv28214
  have hv28216 : v28216 s i = 1 → BitVec.extractLsb' 5 1 (v28577 s i) = 0 := by
    by_cases selected : v26574 s i = 1
    · simp only [v28216, v28577, selected, ↓reduceIte]
      simp [v28116]
    · simpa only [v28216, v28577, selected, ↓reduceIte] using hv28215
  have hv28217 : v28217 s i = 1 → BitVec.extractLsb' 5 1 (v28578 s i) = 0 := by
    by_cases selected : v26569 s i = 1
    · simp only [v28217, v28578, selected, ↓reduceIte]
      intro _
      unfold v28486
      decide
    · simpa only [v28217, v28578, selected, ↓reduceIte] using hv28216
  have hv28218 : v28218 s i = 1 → BitVec.extractLsb' 5 1 (v28579 s i) = 0 := by
    by_cases selected : v26564 s i = 1
    · simp only [v28218, v28579, selected, ↓reduceIte]
      intro _
      unfold v28485
      decide
    · simpa only [v28218, v28579, selected, ↓reduceIte] using hv28217
  have hv28219 : v28219 s i = 1 → BitVec.extractLsb' 5 1 (v28580 s i) = 0 := by
    by_cases selected : v26559 s i = 1
    · simp only [v28219, v28580, selected, ↓reduceIte]
      intro _
      unfold v28484
      decide
    · simpa only [v28219, v28580, selected, ↓reduceIte] using hv28218
  have hv28220 : v28220 s i = 1 → BitVec.extractLsb' 5 1 (v28581 s i) = 0 := by
    by_cases selected : v26554 s i = 1
    · simp only [v28220, v28581, selected, ↓reduceIte]
      intro _
      unfold v28483
      decide
    · simpa only [v28220, v28581, selected, ↓reduceIte] using hv28219
  have hv28221 : v28221 s i = 1 → BitVec.extractLsb' 5 1 (v28582 s i) = 0 := by
    by_cases selected : v26549 s i = 1
    · simp only [v28221, v28582, selected, ↓reduceIte]
      intro _
      unfold v28482
      decide
    · simpa only [v28221, v28582, selected, ↓reduceIte] using hv28220
  have hv28222 : v28222 s i = 1 → BitVec.extractLsb' 5 1 (v28583 s i) = 0 := by
    by_cases selected : v26544 s i = 1
    · simp only [v28222, v28583, selected, ↓reduceIte]
      intro _
      unfold v28481
      decide
    · simpa only [v28222, v28583, selected, ↓reduceIte] using hv28221
  have hv28223 : v28223 s i = 1 → BitVec.extractLsb' 5 1 (v28584 s i) = 0 := by
    by_cases selected : v26539 s i = 1
    · simp only [v28223, v28584, selected, ↓reduceIte]
      intro _
      unfold v28480
      decide
    · simpa only [v28223, v28584, selected, ↓reduceIte] using hv28222
  have hv28224 : v28224 s i = 1 → BitVec.extractLsb' 5 1 (v28585 s i) = 0 := by
    by_cases selected : v26534 s i = 1
    · simp only [v28224, v28585, selected, ↓reduceIte]
      intro _
      unfold v28479
      decide
    · simpa only [v28224, v28585, selected, ↓reduceIte] using hv28223
  have hv28225 : v28225 s i = 1 → BitVec.extractLsb' 5 1 (v28586 s i) = 0 := by
    by_cases selected : v26529 s i = 1
    · simp only [v28225, v28586, selected, ↓reduceIte]
      simp [v28107]
    · simpa only [v28225, v28586, selected, ↓reduceIte] using hv28224
  have hv28226 : v28226 s i = 1 → BitVec.extractLsb' 5 1 (v28587 s i) = 0 := by
    by_cases selected : v26524 s i = 1
    · simp only [v28226, v28587, selected, ↓reduceIte]
      simp [v28106]
    · simpa only [v28226, v28587, selected, ↓reduceIte] using hv28225
  have hv28227 : v28227 s i = 1 → BitVec.extractLsb' 5 1 (v28588 s i) = 0 := by
    by_cases selected : v26519 s i = 1
    · simp only [v28227, v28588, selected, ↓reduceIte]
      simp [v28105]
    · simpa only [v28227, v28588, selected, ↓reduceIte] using hv28226
  have hv28228 : v28228 s i = 1 → BitVec.extractLsb' 5 1 (v28589 s i) = 0 := by
    by_cases selected : v26514 s i = 1
    · simp only [v28228, v28589, selected, ↓reduceIte]
      simp [v28104]
    · simpa only [v28228, v28589, selected, ↓reduceIte] using hv28227
  have hv28229 : v28229 s i = 1 → BitVec.extractLsb' 5 1 (v28590 s i) = 0 := by
    by_cases selected : v26509 s i = 1
    · simp only [v28229, v28590, selected, ↓reduceIte]
      simp [v28103]
    · simpa only [v28229, v28590, selected, ↓reduceIte] using hv28228
  have hv28230 : v28230 s i = 1 → BitVec.extractLsb' 5 1 (v28591 s i) = 0 := by
    by_cases selected : v26504 s i = 1
    · simp only [v28230, v28591, selected, ↓reduceIte]
      simp [v28102]
    · simpa only [v28230, v28591, selected, ↓reduceIte] using hv28229
  have hv28231 : v28231 s i = 1 → BitVec.extractLsb' 5 1 (v28592 s i) = 0 := by
    by_cases selected : v26499 s i = 1
    · simp only [v28231, v28592, selected, ↓reduceIte]
      simp [v28101]
    · simpa only [v28231, v28592, selected, ↓reduceIte] using hv28230
  have hv28232 : v28232 s i = 1 → BitVec.extractLsb' 5 1 (v28593 s i) = 0 := by
    by_cases selected : v26494 s i = 1
    · simp only [v28232, v28593, selected, ↓reduceIte]
      simp [v28100]
    · simpa only [v28232, v28593, selected, ↓reduceIte] using hv28231
  have hv28233 : v28233 s i = 1 → BitVec.extractLsb' 5 1 (v28594 s i) = 0 := by
    by_cases selected : v26489 s i = 1
    · simp only [v28233, v28594, selected, ↓reduceIte]
      simp [v28099]
    · simpa only [v28233, v28594, selected, ↓reduceIte] using hv28232
  have hv28234 : v28234 s i = 1 → BitVec.extractLsb' 5 1 (v28595 s i) = 0 := by
    by_cases selected : v26484 s i = 1
    · simp only [v28234, v28595, selected, ↓reduceIte]
      simp [v28098]
    · simpa only [v28234, v28595, selected, ↓reduceIte] using hv28233
  have hv28235 : v28235 s i = 1 → BitVec.extractLsb' 5 1 (v28596 s i) = 0 := by
    by_cases selected : v26479 s i = 1
    · simp only [v28235, v28596, selected, ↓reduceIte]
      simp [v28097]
    · simpa only [v28235, v28596, selected, ↓reduceIte] using hv28234
  have hv28236 : v28236 s i = 1 → BitVec.extractLsb' 5 1 (v28597 s i) = 0 := by
    by_cases selected : v26474 s i = 1
    · simp only [v28236, v28597, selected, ↓reduceIte]
      simp [v28096]
    · simpa only [v28236, v28597, selected, ↓reduceIte] using hv28235
  have hv28237 : v28237 s i = 1 → BitVec.extractLsb' 5 1 (v28598 s i) = 0 := by
    by_cases selected : v26469 s i = 1
    · simp only [v28237, v28598, selected, ↓reduceIte]
      simp [v28095]
    · simpa only [v28237, v28598, selected, ↓reduceIte] using hv28236
  have hv28238 : v28238 s i = 1 → BitVec.extractLsb' 5 1 (v28599 s i) = 0 := by
    by_cases selected : v26464 s i = 1
    · simp only [v28238, v28599, selected, ↓reduceIte]
      simp [v28094]
    · simpa only [v28238, v28599, selected, ↓reduceIte] using hv28237
  have hv28239 : v28239 s i = 1 → BitVec.extractLsb' 5 1 (v28600 s i) = 0 := by
    by_cases selected : v26459 s i = 1
    · simp only [v28239, v28600, selected, ↓reduceIte]
      simp [v28093]
    · simpa only [v28239, v28600, selected, ↓reduceIte] using hv28238
  have hv28240 : v28240 s i = 1 → BitVec.extractLsb' 5 1 (v28601 s i) = 0 := by
    by_cases selected : v26454 s i = 1
    · simp only [v28240, v28601, selected, ↓reduceIte]
      simp [v28092]
    · simpa only [v28240, v28601, selected, ↓reduceIte] using hv28239
  have hv28241 : v28241 s i = 1 → BitVec.extractLsb' 5 1 (v28602 s i) = 0 := by
    by_cases selected : v26449 s i = 1
    · simp only [v28241, v28602, selected, ↓reduceIte]
      simp [v28091]
    · simpa only [v28241, v28602, selected, ↓reduceIte] using hv28240
  have hv28242 : v28242 s i = 1 → BitVec.extractLsb' 5 1 (v28603 s i) = 0 := by
    by_cases selected : v26444 s i = 1
    · simp only [v28242, v28603, selected, ↓reduceIte]
      simp [v28090]
    · simpa only [v28242, v28603, selected, ↓reduceIte] using hv28241
  have hv28243 : v28243 s i = 1 → BitVec.extractLsb' 5 1 (v28604 s i) = 0 := by
    by_cases selected : v26439 s i = 1
    · simp only [v28243, v28604, selected, ↓reduceIte]
      simp [v28089]
    · simpa only [v28243, v28604, selected, ↓reduceIte] using hv28242
  have hv28244 : v28244 s i = 1 → BitVec.extractLsb' 5 1 (v28605 s i) = 0 := by
    by_cases selected : v26434 s i = 1
    · simp only [v28244, v28605, selected, ↓reduceIte]
      simp [v28088]
    · simpa only [v28244, v28605, selected, ↓reduceIte] using hv28243
  have hv28245 : v28245 s i = 1 → BitVec.extractLsb' 5 1 (v28606 s i) = 0 := by
    by_cases selected : v26429 s i = 1
    · simp only [v28245, v28606, selected, ↓reduceIte]
      simp [v28087]
    · simpa only [v28245, v28606, selected, ↓reduceIte] using hv28244
  have hv28246 : v28246 s i = 1 → BitVec.extractLsb' 5 1 (v28607 s i) = 0 := by
    by_cases selected : v26424 s i = 1
    · simp only [v28246, v28607, selected, ↓reduceIte]
      simp [v28086]
    · simpa only [v28246, v28607, selected, ↓reduceIte] using hv28245
  have hv28247 : v28247 s i = 1 → BitVec.extractLsb' 5 1 (v28608 s i) = 0 := by
    by_cases selected : v26419 s i = 1
    · simp only [v28247, v28608, selected, ↓reduceIte]
      simp [v28085]
    · simpa only [v28247, v28608, selected, ↓reduceIte] using hv28246
  have hv28248 : v28248 s i = 1 → BitVec.extractLsb' 5 1 (v28609 s i) = 0 := by
    by_cases selected : v26414 s i = 1
    · simp only [v28248, v28609, selected, ↓reduceIte]
      simp [v28084]
    · simpa only [v28248, v28609, selected, ↓reduceIte] using hv28247
  have hv28249 : v28249 s i = 1 → BitVec.extractLsb' 5 1 (v28610 s i) = 0 := by
    by_cases selected : v26409 s i = 1
    · simp only [v28249, v28610, selected, ↓reduceIte]
      simp [v28083]
    · simpa only [v28249, v28610, selected, ↓reduceIte] using hv28248
  have hv28250 : v28250 s i = 1 → BitVec.extractLsb' 5 1 (v28611 s i) = 0 := by
    by_cases selected : v26404 s i = 1
    · simp only [v28250, v28611, selected, ↓reduceIte]
      simp [v28082]
    · simpa only [v28250, v28611, selected, ↓reduceIte] using hv28249
  have hv28251 : v28251 s i = 1 → BitVec.extractLsb' 5 1 (v28612 s i) = 0 := by
    by_cases selected : v26399 s i = 1
    · simp only [v28251, v28612, selected, ↓reduceIte]
      simp [v28081]
    · simpa only [v28251, v28612, selected, ↓reduceIte] using hv28250
  have hv28252 : v28252 s i = 1 → BitVec.extractLsb' 5 1 (v28613 s i) = 0 := by
    by_cases selected : v26394 s i = 1
    · simp only [v28252, v28613, selected, ↓reduceIte]
      simp [v28080]
    · simpa only [v28252, v28613, selected, ↓reduceIte] using hv28251
  have hv28253 : v28253 s i = 1 → BitVec.extractLsb' 5 1 (v28614 s i) = 0 := by
    by_cases selected : v26389 s i = 1
    · simp only [v28253, v28614, selected, ↓reduceIte]
      simp [v28079]
    · simpa only [v28253, v28614, selected, ↓reduceIte] using hv28252
  have override : v28454 s i = v28077 s i := rfl
  have hv28254 : v28254 s i = 1 → BitVec.extractLsb' 5 1 (v28615 s i) = 0 := by
    by_cases selected : v28077 s i = 1
    · simp only [v28254, v28615, override, selected, ↓reduceIte]
      simp [v28078]
    · simpa only [v28254, v28615, override, selected, ↓reduceIte] using hv28253
  have result := hv28254 lsu
  simpa only [v28643, v28642, v28641, v28640, v28452, v28451, lsu, ↓reduceIte] using result
#print axioms idu_non_atomic_lsu_decode_0
theorem idu_non_atomic_lsu_decode_1 (s : State) (i : Inputs)
    (nonAtomic : NonAtomicInstruction (v26223 s i)) (lsu : v28438 s i = 1) :
    BitVec.extractLsb' 5 1 (v28836 s i) = 0 := by
  have hv27256 : v27256 s i = 0 := by
    have miss : v27253 s i ≠ v26223 s i &&& v27254 s i := by
      intro matched
      have opcode := opcode_of_mask (v26223 s i) (v27254 s i) (v27253 s i) (by unfold v27254; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v27253 s i) = 47 := by unfold v27253; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv27261 : v27261 s i = 0 := by
    have miss : v27258 s i ≠ v26223 s i &&& v27259 s i := by
      intro matched
      have opcode := opcode_of_mask (v26223 s i) (v27259 s i) (v27258 s i) (by unfold v27259; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v27258 s i) = 47 := by unfold v27258; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv27266 : v27266 s i = 0 := by
    have miss : v27263 s i ≠ v26223 s i &&& v27264 s i := by
      intro matched
      have opcode := opcode_of_mask (v26223 s i) (v27264 s i) (v27263 s i) (by unfold v27264; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v27263 s i) = 47 := by unfold v27263; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv27270 : v27270 s i = 0 := by
    have miss : v27267 s i ≠ v26223 s i &&& v27268 s i := by
      intro matched
      have opcode := opcode_of_mask (v26223 s i) (v27268 s i) (v27267 s i) (by unfold v27268; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v27267 s i) = 47 := by unfold v27267; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv27274 : v27274 s i = 0 := by
    have miss : v27271 s i ≠ v26223 s i &&& v27272 s i := by
      intro matched
      have opcode := opcode_of_mask (v26223 s i) (v27272 s i) (v27271 s i) (by unfold v27272; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v27271 s i) = 47 := by unfold v27271; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv27278 : v27278 s i = 0 := by
    have miss : v27275 s i ≠ v26223 s i &&& v27276 s i := by
      intro matched
      have opcode := opcode_of_mask (v26223 s i) (v27276 s i) (v27275 s i) (by unfold v27276; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v27275 s i) = 47 := by unfold v27275; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv27282 : v27282 s i = 0 := by
    have miss : v27279 s i ≠ v26223 s i &&& v27280 s i := by
      intro matched
      have opcode := opcode_of_mask (v26223 s i) (v27280 s i) (v27279 s i) (by unfold v27280; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v27279 s i) = 47 := by unfold v27279; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv27286 : v27286 s i = 0 := by
    have miss : v27283 s i ≠ v26223 s i &&& v27284 s i := by
      intro matched
      have opcode := opcode_of_mask (v26223 s i) (v27284 s i) (v27283 s i) (by unfold v27284; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v27283 s i) = 47 := by unfold v27283; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv27290 : v27290 s i = 0 := by
    have miss : v27287 s i ≠ v26223 s i &&& v27288 s i := by
      intro matched
      have opcode := opcode_of_mask (v26223 s i) (v27288 s i) (v27287 s i) (by unfold v27288; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v27287 s i) = 47 := by unfold v27287; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv27294 : v27294 s i = 0 := by
    have miss : v27291 s i ≠ v26223 s i &&& v27292 s i := by
      intro matched
      have opcode := opcode_of_mask (v26223 s i) (v27292 s i) (v27291 s i) (by unfold v27292; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v27291 s i) = 47 := by unfold v27291; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv27298 : v27298 s i = 0 := by
    have miss : v27295 s i ≠ v26223 s i &&& v27296 s i := by
      intro matched
      have opcode := opcode_of_mask (v26223 s i) (v27296 s i) (v27295 s i) (by unfold v27296; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v27295 s i) = 47 := by unfold v27295; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv27302 : v27302 s i = 0 := by
    have miss : v27299 s i ≠ v26223 s i &&& v27300 s i := by
      intro matched
      have opcode := opcode_of_mask (v26223 s i) (v27300 s i) (v27299 s i) (by unfold v27300; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v27299 s i) = 47 := by unfold v27299; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have hv27306 : v27306 s i = 0 := by
    have miss : v27303 s i ≠ v26223 s i &&& v27304 s i := by
      intro matched
      have opcode := opcode_of_mask (v26223 s i) (v27304 s i) (v27303 s i) (by unfold v27304; decide) matched
      have atomic : BitVec.extractLsb' 0 7 (v27303 s i) = 47 := by unfold v27303; decide
      exact nonAtomic (opcode.trans atomic)
    exact if_neg miss
  have tail : v28349 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by simp [v28349]
  have hv28350 : v28350 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by
    by_cases selected : v27334 s i = 1
    · simp only [v28350, selected, ↓reduceIte]
      simp [v4]
    · simpa only [v28350, selected, ↓reduceIte] using tail
  have hv28351 : v28351 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by
    by_cases selected : v27330 s i = 1
    · simp only [v28351, selected, ↓reduceIte]
      simp [v28348]
    · simpa only [v28351, selected, ↓reduceIte] using hv28350
  have hv28352 : v28352 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by
    by_cases selected : v27326 s i = 1
    · simp only [v28352, selected, ↓reduceIte]
      simp [v28347]
    · simpa only [v28352, selected, ↓reduceIte] using hv28351
  have hv28353 : v28353 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by
    by_cases selected : v27322 s i = 1
    · simp only [v28353, selected, ↓reduceIte]
      simp [v28346]
    · simpa only [v28353, selected, ↓reduceIte] using hv28352
  have hv28354 : v28354 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by
    by_cases selected : v27318 s i = 1
    · simp only [v28354, selected, ↓reduceIte]
      simp [v28345]
    · simpa only [v28354, selected, ↓reduceIte] using hv28353
  have hv28355 : v28355 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by
    by_cases selected : v27314 s i = 1
    · simp only [v28355, selected, ↓reduceIte]
      simp [v28344]
    · simpa only [v28355, selected, ↓reduceIte] using hv28354
  have hv28356 : v28356 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by
    by_cases selected : v27310 s i = 1
    · simp only [v28356, selected, ↓reduceIte]
      simp [v28343]
    · simpa only [v28356, selected, ↓reduceIte] using hv28355
  have hv28357 : v28357 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by
    simpa only [v28357, hv27306, ↓reduceIte] using hv28356
  have hv28358 : v28358 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by
    simpa only [v28358, hv27302, ↓reduceIte] using hv28357
  have hv28359 : v28359 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by
    simpa only [v28359, hv27298, ↓reduceIte] using hv28358
  have hv28360 : v28360 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by
    simpa only [v28360, hv27294, ↓reduceIte] using hv28359
  have hv28361 : v28361 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by
    simpa only [v28361, hv27290, ↓reduceIte] using hv28360
  have hv28362 : v28362 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by
    simpa only [v28362, hv27286, ↓reduceIte] using hv28361
  have hv28363 : v28363 s i = 1 → BitVec.extractLsb' 5 1 (v28733 s i) = 0 := by
    simpa only [v28363, hv27282, ↓reduceIte] using hv28362
  have hv28364 : v28364 s i = 1 → BitVec.extractLsb' 5 1 (v28734 s i) = 0 := by
    simpa only [v28364, v28734, hv27278, ↓reduceIte] using hv28363
  have hv28365 : v28365 s i = 1 → BitVec.extractLsb' 5 1 (v28735 s i) = 0 := by
    simpa only [v28365, v28735, hv27274, ↓reduceIte] using hv28364
  have hv28366 : v28366 s i = 1 → BitVec.extractLsb' 5 1 (v28736 s i) = 0 := by
    simpa only [v28366, v28736, hv27270, ↓reduceIte] using hv28365
  have hv28367 : v28367 s i = 1 → BitVec.extractLsb' 5 1 (v28737 s i) = 0 := by
    simpa only [v28367, v28737, hv27266, ↓reduceIte] using hv28366
  have hv28368 : v28368 s i = 1 → BitVec.extractLsb' 5 1 (v28738 s i) = 0 := by
    simpa only [v28368, v28738, hv27261, ↓reduceIte] using hv28367
  have hv28369 : v28369 s i = 1 → BitVec.extractLsb' 5 1 (v28739 s i) = 0 := by
    simpa only [v28369, v28739, hv27256, ↓reduceIte] using hv28368
  have hv28370 : v28370 s i = 1 → BitVec.extractLsb' 5 1 (v28740 s i) = 0 := by
    by_cases selected : v27251 s i = 1
    · simp only [v28370, v28740, selected, ↓reduceIte]
      simp [v28329]
    · simpa only [v28370, v28740, selected, ↓reduceIte] using hv28369
  have hv28371 : v28371 s i = 1 → BitVec.extractLsb' 5 1 (v28741 s i) = 0 := by
    by_cases selected : v27246 s i = 1
    · simp only [v28371, v28741, selected, ↓reduceIte]
      simp [v4]
    · simpa only [v28371, v28741, selected, ↓reduceIte] using hv28370
  have hv28372 : v28372 s i = 1 → BitVec.extractLsb' 5 1 (v28742 s i) = 0 := by
    by_cases selected : v27241 s i = 1
    · simp only [v28372, v28742, selected, ↓reduceIte]
      simp [v28328]
    · simpa only [v28372, v28742, selected, ↓reduceIte] using hv28371
  have hv28373 : v28373 s i = 1 → BitVec.extractLsb' 5 1 (v28743 s i) = 0 := by
    by_cases selected : v27236 s i = 1
    · simp only [v28373, v28743, selected, ↓reduceIte]
      simp [v28327]
    · simpa only [v28373, v28743, selected, ↓reduceIte] using hv28372
  have hv28374 : v28374 s i = 1 → BitVec.extractLsb' 5 1 (v28744 s i) = 0 := by
    by_cases selected : v27231 s i = 1
    · simp only [v28374, v28744, selected, ↓reduceIte]
      simp [v28326]
    · simpa only [v28374, v28744, selected, ↓reduceIte] using hv28373
  have hv28375 : v28375 s i = 1 → BitVec.extractLsb' 5 1 (v28745 s i) = 0 := by
    by_cases selected : v27226 s i = 1
    · simp only [v28375, v28745, selected, ↓reduceIte]
      simp [v28325]
    · simpa only [v28375, v28745, selected, ↓reduceIte] using hv28374
  have hv28376 : v28376 s i = 1 → BitVec.extractLsb' 5 1 (v28746 s i) = 0 := by
    by_cases selected : v27221 s i = 1
    · simp only [v28376, v28746, selected, ↓reduceIte]
      simp [v28324]
    · simpa only [v28376, v28746, selected, ↓reduceIte] using hv28375
  have hv28377 : v28377 s i = 1 → BitVec.extractLsb' 5 1 (v28747 s i) = 0 := by
    by_cases selected : v27216 s i = 1
    · simp only [v28377, v28747, selected, ↓reduceIte]
      simp [v28323]
    · simpa only [v28377, v28747, selected, ↓reduceIte] using hv28376
  have hv28378 : v28378 s i = 1 → BitVec.extractLsb' 5 1 (v28748 s i) = 0 := by
    by_cases selected : v27211 s i = 1
    · simp only [v28378, v28748, selected, ↓reduceIte]
      simp [v28322]
    · simpa only [v28378, v28748, selected, ↓reduceIte] using hv28377
  have hv28379 : v28379 s i = 1 → BitVec.extractLsb' 5 1 (v28749 s i) = 0 := by
    by_cases selected : v27206 s i = 1
    · simp only [v28379, v28749, selected, ↓reduceIte]
      simp [v28321]
    · simpa only [v28379, v28749, selected, ↓reduceIte] using hv28378
  have hv28380 : v28380 s i = 1 → BitVec.extractLsb' 5 1 (v28750 s i) = 0 := by
    by_cases selected : v27201 s i = 1
    · simp only [v28380, v28750, selected, ↓reduceIte]
      simp [v28320]
    · simpa only [v28380, v28750, selected, ↓reduceIte] using hv28379
  have hv28381 : v28381 s i = 1 → BitVec.extractLsb' 5 1 (v28751 s i) = 0 := by
    by_cases selected : v27196 s i = 1
    · simp only [v28381, v28751, selected, ↓reduceIte]
      simp [v28319]
    · simpa only [v28381, v28751, selected, ↓reduceIte] using hv28380
  have hv28382 : v28382 s i = 1 → BitVec.extractLsb' 5 1 (v28752 s i) = 0 := by
    by_cases selected : v27191 s i = 1
    · simp only [v28382, v28752, selected, ↓reduceIte]
      simp [v28318]
    · simpa only [v28382, v28752, selected, ↓reduceIte] using hv28381
  have hv28383 : v28383 s i = 1 → BitVec.extractLsb' 5 1 (v28753 s i) = 0 := by
    by_cases selected : v27186 s i = 1
    · simp only [v28383, v28753, selected, ↓reduceIte]
      simp [v28317]
    · simpa only [v28383, v28753, selected, ↓reduceIte] using hv28382
  have hv28384 : v28384 s i = 1 → BitVec.extractLsb' 5 1 (v28754 s i) = 0 := by
    by_cases selected : v27181 s i = 1
    · simp only [v28384, v28754, selected, ↓reduceIte]
      simp [v28316]
    · simpa only [v28384, v28754, selected, ↓reduceIte] using hv28383
  have hv28385 : v28385 s i = 1 → BitVec.extractLsb' 5 1 (v28755 s i) = 0 := by
    by_cases selected : v27176 s i = 1
    · simp only [v28385, v28755, selected, ↓reduceIte]
      simp [v28315]
    · simpa only [v28385, v28755, selected, ↓reduceIte] using hv28384
  have hv28386 : v28386 s i = 1 → BitVec.extractLsb' 5 1 (v28756 s i) = 0 := by
    by_cases selected : v27171 s i = 1
    · simp only [v28386, v28756, selected, ↓reduceIte]
      simp [v28314]
    · simpa only [v28386, v28756, selected, ↓reduceIte] using hv28385
  have hv28387 : v28387 s i = 1 → BitVec.extractLsb' 5 1 (v28757 s i) = 0 := by
    by_cases selected : v27166 s i = 1
    · simp only [v28387, v28757, selected, ↓reduceIte]
      simp [v28313]
    · simpa only [v28387, v28757, selected, ↓reduceIte] using hv28386
  have hv28388 : v28388 s i = 1 → BitVec.extractLsb' 5 1 (v28758 s i) = 0 := by
    by_cases selected : v27161 s i = 1
    · simp only [v28388, v28758, selected, ↓reduceIte]
      simp [v28312]
    · simpa only [v28388, v28758, selected, ↓reduceIte] using hv28387
  have hv28389 : v28389 s i = 1 → BitVec.extractLsb' 5 1 (v28759 s i) = 0 := by
    by_cases selected : v27156 s i = 1
    · simp only [v28389, v28759, selected, ↓reduceIte]
      intro _
      unfold v28691
      decide
    · simpa only [v28389, v28759, selected, ↓reduceIte] using hv28388
  have hv28390 : v28390 s i = 1 → BitVec.extractLsb' 5 1 (v28760 s i) = 0 := by
    by_cases selected : v27151 s i = 1
    · simp only [v28390, v28760, selected, ↓reduceIte]
      intro _
      unfold v28690
      decide
    · simpa only [v28390, v28760, selected, ↓reduceIte] using hv28389
  have hv28391 : v28391 s i = 1 → BitVec.extractLsb' 5 1 (v28761 s i) = 0 := by
    by_cases selected : v27146 s i = 1
    · simp only [v28391, v28761, selected, ↓reduceIte]
      intro _
      unfold v28689
      decide
    · simpa only [v28391, v28761, selected, ↓reduceIte] using hv28390
  have hv28392 : v28392 s i = 1 → BitVec.extractLsb' 5 1 (v28762 s i) = 0 := by
    by_cases selected : v27141 s i = 1
    · simp only [v28392, v28762, selected, ↓reduceIte]
      simp [v28308]
    · simpa only [v28392, v28762, selected, ↓reduceIte] using hv28391
  have hv28393 : v28393 s i = 1 → BitVec.extractLsb' 5 1 (v28763 s i) = 0 := by
    by_cases selected : v27136 s i = 1
    · simp only [v28393, v28763, selected, ↓reduceIte]
      simp [v28307]
    · simpa only [v28393, v28763, selected, ↓reduceIte] using hv28392
  have hv28394 : v28394 s i = 1 → BitVec.extractLsb' 5 1 (v28764 s i) = 0 := by
    by_cases selected : v27131 s i = 1
    · simp only [v28394, v28764, selected, ↓reduceIte]
      simp [v28306]
    · simpa only [v28394, v28764, selected, ↓reduceIte] using hv28393
  have hv28395 : v28395 s i = 1 → BitVec.extractLsb' 5 1 (v28765 s i) = 0 := by
    by_cases selected : v27126 s i = 1
    · simp only [v28395, v28765, selected, ↓reduceIte]
      simp [v28305]
    · simpa only [v28395, v28765, selected, ↓reduceIte] using hv28394
  have hv28396 : v28396 s i = 1 → BitVec.extractLsb' 5 1 (v28766 s i) = 0 := by
    by_cases selected : v27121 s i = 1
    · simp only [v28396, v28766, selected, ↓reduceIte]
      simp [v28304]
    · simpa only [v28396, v28766, selected, ↓reduceIte] using hv28395
  have hv28397 : v28397 s i = 1 → BitVec.extractLsb' 5 1 (v28767 s i) = 0 := by
    by_cases selected : v27116 s i = 1
    · simp only [v28397, v28767, selected, ↓reduceIte]
      simp [v28303]
    · simpa only [v28397, v28767, selected, ↓reduceIte] using hv28396
  have hv28398 : v28398 s i = 1 → BitVec.extractLsb' 5 1 (v28768 s i) = 0 := by
    by_cases selected : v27111 s i = 1
    · simp only [v28398, v28768, selected, ↓reduceIte]
      simp [v28302]
    · simpa only [v28398, v28768, selected, ↓reduceIte] using hv28397
  have hv28399 : v28399 s i = 1 → BitVec.extractLsb' 5 1 (v28769 s i) = 0 := by
    by_cases selected : v27106 s i = 1
    · simp only [v28399, v28769, selected, ↓reduceIte]
      simp [v28301]
    · simpa only [v28399, v28769, selected, ↓reduceIte] using hv28398
  have hv28400 : v28400 s i = 1 → BitVec.extractLsb' 5 1 (v28770 s i) = 0 := by
    by_cases selected : v27101 s i = 1
    · simp only [v28400, v28770, selected, ↓reduceIte]
      simp [v28300]
    · simpa only [v28400, v28770, selected, ↓reduceIte] using hv28399
  have hv28401 : v28401 s i = 1 → BitVec.extractLsb' 5 1 (v28771 s i) = 0 := by
    by_cases selected : v27096 s i = 1
    · simp only [v28401, v28771, selected, ↓reduceIte]
      intro _
      unfold v28681
      decide
    · simpa only [v28401, v28771, selected, ↓reduceIte] using hv28400
  have hv28402 : v28402 s i = 1 → BitVec.extractLsb' 5 1 (v28772 s i) = 0 := by
    by_cases selected : v27091 s i = 1
    · simp only [v28402, v28772, selected, ↓reduceIte]
      intro _
      unfold v28680
      decide
    · simpa only [v28402, v28772, selected, ↓reduceIte] using hv28401
  have hv28403 : v28403 s i = 1 → BitVec.extractLsb' 5 1 (v28773 s i) = 0 := by
    by_cases selected : v27086 s i = 1
    · simp only [v28403, v28773, selected, ↓reduceIte]
      intro _
      unfold v28679
      decide
    · simpa only [v28403, v28773, selected, ↓reduceIte] using hv28402
  have hv28404 : v28404 s i = 1 → BitVec.extractLsb' 5 1 (v28774 s i) = 0 := by
    by_cases selected : v27081 s i = 1
    · simp only [v28404, v28774, selected, ↓reduceIte]
      intro _
      unfold v28678
      decide
    · simpa only [v28404, v28774, selected, ↓reduceIte] using hv28403
  have hv28405 : v28405 s i = 1 → BitVec.extractLsb' 5 1 (v28775 s i) = 0 := by
    by_cases selected : v27076 s i = 1
    · simp only [v28405, v28775, selected, ↓reduceIte]
      intro _
      unfold v28677
      decide
    · simpa only [v28405, v28775, selected, ↓reduceIte] using hv28404
  have hv28406 : v28406 s i = 1 → BitVec.extractLsb' 5 1 (v28776 s i) = 0 := by
    by_cases selected : v27071 s i = 1
    · simp only [v28406, v28776, selected, ↓reduceIte]
      intro _
      unfold v28676
      decide
    · simpa only [v28406, v28776, selected, ↓reduceIte] using hv28405
  have hv28407 : v28407 s i = 1 → BitVec.extractLsb' 5 1 (v28777 s i) = 0 := by
    by_cases selected : v27066 s i = 1
    · simp only [v28407, v28777, selected, ↓reduceIte]
      intro _
      unfold v28675
      decide
    · simpa only [v28407, v28777, selected, ↓reduceIte] using hv28406
  have hv28408 : v28408 s i = 1 → BitVec.extractLsb' 5 1 (v28778 s i) = 0 := by
    by_cases selected : v27061 s i = 1
    · simp only [v28408, v28778, selected, ↓reduceIte]
      intro _
      unfold v28674
      decide
    · simpa only [v28408, v28778, selected, ↓reduceIte] using hv28407
  have hv28409 : v28409 s i = 1 → BitVec.extractLsb' 5 1 (v28779 s i) = 0 := by
    by_cases selected : v27056 s i = 1
    · simp only [v28409, v28779, selected, ↓reduceIte]
      simp [v28291]
    · simpa only [v28409, v28779, selected, ↓reduceIte] using hv28408
  have hv28410 : v28410 s i = 1 → BitVec.extractLsb' 5 1 (v28780 s i) = 0 := by
    by_cases selected : v27051 s i = 1
    · simp only [v28410, v28780, selected, ↓reduceIte]
      simp [v28290]
    · simpa only [v28410, v28780, selected, ↓reduceIte] using hv28409
  have hv28411 : v28411 s i = 1 → BitVec.extractLsb' 5 1 (v28781 s i) = 0 := by
    by_cases selected : v27046 s i = 1
    · simp only [v28411, v28781, selected, ↓reduceIte]
      simp [v28289]
    · simpa only [v28411, v28781, selected, ↓reduceIte] using hv28410
  have hv28412 : v28412 s i = 1 → BitVec.extractLsb' 5 1 (v28782 s i) = 0 := by
    by_cases selected : v27041 s i = 1
    · simp only [v28412, v28782, selected, ↓reduceIte]
      simp [v28288]
    · simpa only [v28412, v28782, selected, ↓reduceIte] using hv28411
  have hv28413 : v28413 s i = 1 → BitVec.extractLsb' 5 1 (v28783 s i) = 0 := by
    by_cases selected : v27036 s i = 1
    · simp only [v28413, v28783, selected, ↓reduceIte]
      simp [v28287]
    · simpa only [v28413, v28783, selected, ↓reduceIte] using hv28412
  have hv28414 : v28414 s i = 1 → BitVec.extractLsb' 5 1 (v28784 s i) = 0 := by
    by_cases selected : v27031 s i = 1
    · simp only [v28414, v28784, selected, ↓reduceIte]
      simp [v28286]
    · simpa only [v28414, v28784, selected, ↓reduceIte] using hv28413
  have hv28415 : v28415 s i = 1 → BitVec.extractLsb' 5 1 (v28785 s i) = 0 := by
    by_cases selected : v27026 s i = 1
    · simp only [v28415, v28785, selected, ↓reduceIte]
      simp [v28285]
    · simpa only [v28415, v28785, selected, ↓reduceIte] using hv28414
  have hv28416 : v28416 s i = 1 → BitVec.extractLsb' 5 1 (v28786 s i) = 0 := by
    by_cases selected : v27021 s i = 1
    · simp only [v28416, v28786, selected, ↓reduceIte]
      simp [v28284]
    · simpa only [v28416, v28786, selected, ↓reduceIte] using hv28415
  have hv28417 : v28417 s i = 1 → BitVec.extractLsb' 5 1 (v28787 s i) = 0 := by
    by_cases selected : v27016 s i = 1
    · simp only [v28417, v28787, selected, ↓reduceIte]
      simp [v28283]
    · simpa only [v28417, v28787, selected, ↓reduceIte] using hv28416
  have hv28418 : v28418 s i = 1 → BitVec.extractLsb' 5 1 (v28788 s i) = 0 := by
    by_cases selected : v27011 s i = 1
    · simp only [v28418, v28788, selected, ↓reduceIte]
      simp [v28282]
    · simpa only [v28418, v28788, selected, ↓reduceIte] using hv28417
  have hv28419 : v28419 s i = 1 → BitVec.extractLsb' 5 1 (v28789 s i) = 0 := by
    by_cases selected : v27006 s i = 1
    · simp only [v28419, v28789, selected, ↓reduceIte]
      simp [v28281]
    · simpa only [v28419, v28789, selected, ↓reduceIte] using hv28418
  have hv28420 : v28420 s i = 1 → BitVec.extractLsb' 5 1 (v28790 s i) = 0 := by
    by_cases selected : v27001 s i = 1
    · simp only [v28420, v28790, selected, ↓reduceIte]
      simp [v28280]
    · simpa only [v28420, v28790, selected, ↓reduceIte] using hv28419
  have hv28421 : v28421 s i = 1 → BitVec.extractLsb' 5 1 (v28791 s i) = 0 := by
    by_cases selected : v26996 s i = 1
    · simp only [v28421, v28791, selected, ↓reduceIte]
      simp [v28279]
    · simpa only [v28421, v28791, selected, ↓reduceIte] using hv28420
  have hv28422 : v28422 s i = 1 → BitVec.extractLsb' 5 1 (v28792 s i) = 0 := by
    by_cases selected : v26991 s i = 1
    · simp only [v28422, v28792, selected, ↓reduceIte]
      simp [v28278]
    · simpa only [v28422, v28792, selected, ↓reduceIte] using hv28421
  have hv28423 : v28423 s i = 1 → BitVec.extractLsb' 5 1 (v28793 s i) = 0 := by
    by_cases selected : v26986 s i = 1
    · simp only [v28423, v28793, selected, ↓reduceIte]
      simp [v28277]
    · simpa only [v28423, v28793, selected, ↓reduceIte] using hv28422
  have hv28424 : v28424 s i = 1 → BitVec.extractLsb' 5 1 (v28794 s i) = 0 := by
    by_cases selected : v26981 s i = 1
    · simp only [v28424, v28794, selected, ↓reduceIte]
      simp [v28276]
    · simpa only [v28424, v28794, selected, ↓reduceIte] using hv28423
  have hv28425 : v28425 s i = 1 → BitVec.extractLsb' 5 1 (v28795 s i) = 0 := by
    by_cases selected : v26976 s i = 1
    · simp only [v28425, v28795, selected, ↓reduceIte]
      simp [v28275]
    · simpa only [v28425, v28795, selected, ↓reduceIte] using hv28424
  have hv28426 : v28426 s i = 1 → BitVec.extractLsb' 5 1 (v28796 s i) = 0 := by
    by_cases selected : v26971 s i = 1
    · simp only [v28426, v28796, selected, ↓reduceIte]
      simp [v28274]
    · simpa only [v28426, v28796, selected, ↓reduceIte] using hv28425
  have hv28427 : v28427 s i = 1 → BitVec.extractLsb' 5 1 (v28797 s i) = 0 := by
    by_cases selected : v26966 s i = 1
    · simp only [v28427, v28797, selected, ↓reduceIte]
      simp [v28273]
    · simpa only [v28427, v28797, selected, ↓reduceIte] using hv28426
  have hv28428 : v28428 s i = 1 → BitVec.extractLsb' 5 1 (v28798 s i) = 0 := by
    by_cases selected : v26961 s i = 1
    · simp only [v28428, v28798, selected, ↓reduceIte]
      simp [v28272]
    · simpa only [v28428, v28798, selected, ↓reduceIte] using hv28427
  have hv28429 : v28429 s i = 1 → BitVec.extractLsb' 5 1 (v28799 s i) = 0 := by
    by_cases selected : v26956 s i = 1
    · simp only [v28429, v28799, selected, ↓reduceIte]
      simp [v28271]
    · simpa only [v28429, v28799, selected, ↓reduceIte] using hv28428
  have hv28430 : v28430 s i = 1 → BitVec.extractLsb' 5 1 (v28800 s i) = 0 := by
    by_cases selected : v26951 s i = 1
    · simp only [v28430, v28800, selected, ↓reduceIte]
      simp [v28270]
    · simpa only [v28430, v28800, selected, ↓reduceIte] using hv28429
  have hv28431 : v28431 s i = 1 → BitVec.extractLsb' 5 1 (v28801 s i) = 0 := by
    by_cases selected : v26946 s i = 1
    · simp only [v28431, v28801, selected, ↓reduceIte]
      simp [v28269]
    · simpa only [v28431, v28801, selected, ↓reduceIte] using hv28430
  have hv28432 : v28432 s i = 1 → BitVec.extractLsb' 5 1 (v28802 s i) = 0 := by
    by_cases selected : v26941 s i = 1
    · simp only [v28432, v28802, selected, ↓reduceIte]
      simp [v28268]
    · simpa only [v28432, v28802, selected, ↓reduceIte] using hv28431
  have hv28433 : v28433 s i = 1 → BitVec.extractLsb' 5 1 (v28803 s i) = 0 := by
    by_cases selected : v26936 s i = 1
    · simp only [v28433, v28803, selected, ↓reduceIte]
      simp [v28267]
    · simpa only [v28433, v28803, selected, ↓reduceIte] using hv28432
  have hv28434 : v28434 s i = 1 → BitVec.extractLsb' 5 1 (v28804 s i) = 0 := by
    by_cases selected : v26931 s i = 1
    · simp only [v28434, v28804, selected, ↓reduceIte]
      simp [v28266]
    · simpa only [v28434, v28804, selected, ↓reduceIte] using hv28433
  have hv28435 : v28435 s i = 1 → BitVec.extractLsb' 5 1 (v28805 s i) = 0 := by
    by_cases selected : v26926 s i = 1
    · simp only [v28435, v28805, selected, ↓reduceIte]
      simp [v28265]
    · simpa only [v28435, v28805, selected, ↓reduceIte] using hv28434
  have hv28436 : v28436 s i = 1 → BitVec.extractLsb' 5 1 (v28806 s i) = 0 := by
    by_cases selected : v26921 s i = 1
    · simp only [v28436, v28806, selected, ↓reduceIte]
      simp [v28264]
    · simpa only [v28436, v28806, selected, ↓reduceIte] using hv28435
  have hv28437 : v28437 s i = 1 → BitVec.extractLsb' 5 1 (v28807 s i) = 0 := by
    by_cases selected : v26916 s i = 1
    · simp only [v28437, v28807, selected, ↓reduceIte]
      simp [v28263]
    · simpa only [v28437, v28807, selected, ↓reduceIte] using hv28436
  have override : v28649 s i = v28261 s i := rfl
  have hv28438 : v28438 s i = 1 → BitVec.extractLsb' 5 1 (v28808 s i) = 0 := by
    by_cases selected : v28261 s i = 1
    · simp only [v28438, v28808, override, selected, ↓reduceIte]
      simp [v28262]
    · simpa only [v28438, v28808, override, selected, ↓reduceIte] using hv28437
  have result := hv28438 lsu
  simpa only [v28836, v28835, v28834, v28833, v28647, v28646, lsu, ↓reduceIte] using result
#print axioms idu_non_atomic_lsu_decode_1
end NutShellProofs
