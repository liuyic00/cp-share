import Proofs.Contract
namespace RiscvMiniProofs
open nCoreSoc
inductive SupportedInstruction (instruction : BitVec 32) : Prop where
  | op_addi : instruction &&& 28799 = 19 → SupportedInstruction instruction
  | op_slti : instruction &&& 28799 = 8211 → SupportedInstruction instruction
  | op_sltiu : instruction &&& 28799 = 12307 → SupportedInstruction instruction
  | op_andi : instruction &&& 28799 = 28691 → SupportedInstruction instruction
  | op_ori : instruction &&& 28799 = 24595 → SupportedInstruction instruction
  | op_xori : instruction &&& 28799 = 16403 → SupportedInstruction instruction
  | op_slli : instruction &&& 4261441663 = 4115 → SupportedInstruction instruction
  | op_srli : instruction &&& 4261441663 = 20499 → SupportedInstruction instruction
  | op_srai : instruction &&& 4261441663 = 1073762323 → SupportedInstruction instruction
  | op_lui : instruction &&& 127 = 55 → SupportedInstruction instruction
  | op_auipc : instruction &&& 127 = 23 → SupportedInstruction instruction
  | op_add : instruction &&& 4261441663 = 51 → SupportedInstruction instruction
  | op_slt : instruction &&& 4261441663 = 8243 → SupportedInstruction instruction
  | op_sltu : instruction &&& 4261441663 = 12339 → SupportedInstruction instruction
  | op_and : instruction &&& 4261441663 = 28723 → SupportedInstruction instruction
  | op_or : instruction &&& 4261441663 = 24627 → SupportedInstruction instruction
  | op_xor : instruction &&& 4261441663 = 16435 → SupportedInstruction instruction
  | op_sll : instruction &&& 4261441663 = 4147 → SupportedInstruction instruction
  | op_srl : instruction &&& 4261441663 = 20531 → SupportedInstruction instruction
  | op_sub : instruction &&& 4261441663 = 1073741875 → SupportedInstruction instruction
  | op_sra : instruction &&& 4261441663 = 1073762355 → SupportedInstruction instruction
  | op_jal : instruction &&& 127 = 111 → SupportedInstruction instruction
  | op_jalr : instruction &&& 28799 = 103 → SupportedInstruction instruction
  | op_beq : instruction &&& 28799 = 99 → SupportedInstruction instruction
  | op_bne : instruction &&& 28799 = 4195 → SupportedInstruction instruction
  | op_blt : instruction &&& 28799 = 16483 → SupportedInstruction instruction
  | op_bltu : instruction &&& 28799 = 24675 → SupportedInstruction instruction
  | op_bge : instruction &&& 28799 = 20579 → SupportedInstruction instruction
  | op_bgeu : instruction &&& 28799 = 28771 → SupportedInstruction instruction
  | op_lb : instruction &&& 28799 = 3 → SupportedInstruction instruction
  | op_lh : instruction &&& 28799 = 4099 → SupportedInstruction instruction
  | op_lw : instruction &&& 28799 = 8195 → SupportedInstruction instruction
  | op_lbu : instruction &&& 28799 = 16387 → SupportedInstruction instruction
  | op_lhu : instruction &&& 28799 = 20483 → SupportedInstruction instruction
  | op_sb : instruction &&& 28799 = 35 → SupportedInstruction instruction
  | op_sh : instruction &&& 28799 = 4131 → SupportedInstruction instruction
  | op_sw : instruction &&& 28799 = 8227 → SupportedInstruction instruction

private theorem bit_or_one (a b : BitVec 1) : a ||| b = 1#1 ↔ a = 1#1 ∨ b = 1#1 := by
  rcases BitVec.eq_zero_or_eq_one a with ha | ha <;>
    rcases BitVec.eq_zero_or_eq_one b with hb | hb <;> simp [ha, hb]

theorem environment_supported_at_commit (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (commit : v964 s i = 1) :
    SupportedInstruction s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  have valid : v9040 s i = 1#1 := commit
  have instruction : v9046 s i = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
    simp [v9046, v9045, v9044, v9043, v512, valid]
  have allowed : v9797 s i = 1#1 := by
    by_cases h : v9797 s i = 1#1
    · exact h
    · rcases BitVec.eq_zero_or_eq_one (v9797 s i) with hz | ho
      · simp [assumes, eval, assumptionChecks, assumptionChecks0,
          v9801, v9800, v9799, v4, reset, hz] at env
      · exact False.elim (h ho)
  simp only [v4, v9625, v9626, v9627, v9628, v9629, v9630, v9631, v9632, v9633, v9634, v9635, v9636, v9637, v9638, v9639, v9640, v9641, v9642, v9643, v9644, v9645, v9646, v9647, v9648, v9649, v9650, v9651, v9652, v9653, v9654, v9655, v9656, v9657, v9658, v9659, v9660, v9661, v9662, v9663, v9664, v9665, v9666, v9667, v9668, v9669, v9670, v9671, v9672, v9673, v9674, v9675, v9676, v9677, v9678, v9679, v9680, v9681, v9682, v9683, v9684, v9685, v9686, v9687, v9688, v9689, v9690, v9691, v9692, v9693, v9694, v9695, v9696, v9697, v9698, v9699, v9700, v9701, v9702, v9703, v9704, v9705, v9706, v9707, v9708, v9709, v9710, v9711, v9712, v9713, v9714, v9715, v9716, v9717, v9718, v9719, v9720, v9721, v9722, v9723, v9724, v9725, v9726, v9727, v9728, v9729, v9730, v9731, v9732, v9733, v9734, v9735, v9736, v9737, v9738, v9739, v9740, v9741, v9742, v9743, v9744, v9745, v9746, v9747, v9748, v9749, v9750, v9751, v9752, v9753, v9754, v9755, v9756, v9757, v9758, v9759, v9760, v9761, v9762, v9763, v9764, v9765, v9766, v9767, v9768, v9769, v9770, v9771, v9772, v9773, v9774, v9775, v9776, v9777, v9778, v9779, v978, v9780, v9781, v9782, v9783, v9784, v9785, v9786, v9787, v9788, v9789, v9790, v9791, v9792, v9793, v9794, v9795, v9796, v9797, valid, instruction, BitVec.reduceEq,
    ↓reduceIte, bit_or_one, Bool.false_eq_true, false_or, or_false, or_assoc] at allowed
  rcases allowed with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have eq : (19 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_addi eq.symm
  · have eq : (8211 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_slti eq.symm
  · have eq : (12307 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_sltiu eq.symm
  · have eq : (28691 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_andi eq.symm
  · have eq : (24595 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_ori eq.symm
  · have eq : (16403 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_xori eq.symm
  · have eq : (4115 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 := by simpa using h
    exact SupportedInstruction.op_slli eq.symm
  · have eq : (20499 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 := by simpa using h
    exact SupportedInstruction.op_srli eq.symm
  · have eq : (1073762323 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 := by simpa using h
    exact SupportedInstruction.op_srai eq.symm
  · have eq : (55 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 := by simpa using h
    exact SupportedInstruction.op_lui eq.symm
  · have eq : (23 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 := by simpa using h
    exact SupportedInstruction.op_auipc eq.symm
  · have eq : (51 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 := by simpa using h
    exact SupportedInstruction.op_add eq.symm
  · have eq : (8243 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 := by simpa using h
    exact SupportedInstruction.op_slt eq.symm
  · have eq : (12339 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 := by simpa using h
    exact SupportedInstruction.op_sltu eq.symm
  · have eq : (28723 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 := by simpa using h
    exact SupportedInstruction.op_and eq.symm
  · have eq : (24627 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 := by simpa using h
    exact SupportedInstruction.op_or eq.symm
  · have eq : (16435 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 := by simpa using h
    exact SupportedInstruction.op_xor eq.symm
  · have eq : (4147 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 := by simpa using h
    exact SupportedInstruction.op_sll eq.symm
  · have eq : (20531 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 := by simpa using h
    exact SupportedInstruction.op_srl eq.symm
  · have eq : (1073741875 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 := by simpa using h
    exact SupportedInstruction.op_sub eq.symm
  · have eq : (1073762355 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 := by simpa using h
    exact SupportedInstruction.op_sra eq.symm
  · have eq : (111 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 := by simpa using h
    exact SupportedInstruction.op_jal eq.symm
  · have eq : (103 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_jalr eq.symm
  · have eq : (99 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_beq eq.symm
  · have eq : (4195 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_bne eq.symm
  · have eq : (16483 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_blt eq.symm
  · have eq : (24675 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_bltu eq.symm
  · have eq : (20579 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_bge eq.symm
  · have eq : (28771 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_bgeu eq.symm
  · have eq : (3 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_lb eq.symm
  · have eq : (4099 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_lh eq.symm
  · have eq : (8195 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_lw eq.symm
  · have eq : (16387 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_lbu eq.symm
  · have eq : (20483 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_lhu eq.symm
  · have eq : (35 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_sb eq.symm
  · have eq : (4131 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_sh eq.symm
  · have eq : (8227 : BitVec 32) = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 := by simpa using h
    exact SupportedInstruction.op_sw eq.symm
#print axioms environment_supported_at_commit
end RiscvMiniProofs
