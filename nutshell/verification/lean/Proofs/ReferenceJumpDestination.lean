import Proofs.CommittedJumpImmediate
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem reference_jump_jal_destination (s : State) (i : Inputs)
    (commit : v9 s i = 1)
    (matched : v14575 s i &&& BitVec.ofNat 32 127 = BitVec.ofNat 32 111) :
    v15142 s i = BitVec.extractLsb' 7 5 (v14575 s i) := by
  have hit : v14909 s i = 1 := by simp [v14909, v14906, v14908, v14907, matched]
  simp only [v15142, v14560, v14559, v14558, v15141, v15140, v15139, v15138, v15137, v15136, v15135, v15134, v15133, v15132, v15131, v15130, v15129, v15128, v15127, v15126, v15125, v15124, v15123, v15122, v15121, v15120, v15119, v15118, v15117, v15116, v15115, v15114, v15113, v15112, v15111, v15110, v15109, v15108, v15107, v15106, v15105, v15104, v15103, v15102, v15101, v15100, v15099, v15098, v14914, v14913, v14912, v14911, v14910, v15076, commit, hit, reference_jump_imm_jal_not_v14578 s i matched, reference_jump_imm_jal_not_v14583 s i matched, reference_jump_imm_jal_not_v14589 s i matched, reference_jump_imm_jal_not_v14595 s i matched, reference_jump_imm_jal_not_v14601 s i matched, reference_jump_imm_jal_not_v14613 s i matched, reference_jump_imm_jal_not_v14621 s i matched, reference_jump_imm_jal_not_v14629 s i matched, reference_jump_imm_jal_not_v14637 s i matched, reference_jump_imm_jal_not_v14645 s i matched, reference_jump_imm_jal_not_v14653 s i matched, reference_jump_imm_jal_not_v14661 s i matched, reference_jump_imm_jal_not_v14669 s i matched, reference_jump_imm_jal_not_v14677 s i matched, reference_jump_imm_jal_not_v14685 s i matched, reference_jump_imm_jal_not_v14693 s i matched, reference_jump_imm_jal_not_v14701 s i matched, reference_jump_imm_jal_not_v14710 s i matched, reference_jump_imm_jal_not_v14718 s i matched, reference_jump_imm_jal_not_v14725 s i matched, reference_jump_imm_jal_not_v14733 s i matched, reference_jump_imm_jal_not_v14741 s i matched, reference_jump_imm_jal_not_v14749 s i matched, reference_jump_imm_jal_not_v14757 s i matched, reference_jump_imm_jal_not_v14765 s i matched, reference_jump_imm_jal_not_v14773 s i matched, reference_jump_imm_jal_not_v14781 s i matched, reference_jump_imm_jal_not_v14789 s i matched, reference_jump_imm_jal_not_v14796 s i matched, reference_jump_imm_jal_not_v14803 s i matched, reference_jump_imm_jal_not_v14811 s i matched, reference_jump_imm_jal_not_v14818 s i matched, reference_jump_imm_jal_not_v14825 s i matched, reference_jump_imm_jal_not_v14833 s i matched, reference_jump_imm_jal_not_v14841 s i matched, reference_jump_imm_jal_not_v14847 s i matched, reference_jump_imm_jal_not_v14853 s i matched, reference_jump_imm_jal_not_v14861 s i matched, reference_jump_imm_jal_not_v14869 s i matched, reference_jump_imm_jal_not_v14877 s i matched, reference_jump_imm_jal_not_v14885 s i matched, reference_jump_imm_jal_not_v14893 s i matched, reference_jump_imm_jal_not_v14901 s i matched, reference_jump_imm_jal_not_v14917 s i matched, reference_jump_imm_jal_not_v14925 s i matched, reference_jump_imm_jal_not_v14933 s i matched, reference_jump_imm_jal_not_v14941 s i matched, reference_jump_imm_jal_not_v14949 s i matched, reference_jump_imm_jal_not_v14957 s i matched, reference_jump_imm_jal_not_v14965 s i matched, reference_jump_imm_jal_not_v14973 s i matched, reference_jump_imm_jal_not_v14981 s i matched, reference_jump_imm_jal_not_v14989 s i matched, reference_jump_imm_jal_not_v14998 s i matched, reference_jump_imm_jal_not_v15004 s i matched, reference_jump_imm_jal_not_v15009 s i matched, reference_jump_imm_jal_not_v15016 s i matched, reference_jump_imm_jal_not_v15023 s i matched, reference_jump_imm_jal_not_v15031 s i matched, reference_jump_imm_jal_not_v15039 s i matched, reference_jump_imm_jal_not_v15047 s i matched, reference_jump_imm_jal_not_v15055 s i matched, reference_jump_imm_jal_not_v15063 s i matched, reference_jump_imm_jal_not_v15071 s i matched, reference_jump_imm_jal_not_v15160 s i matched, reference_jump_imm_jal_not_v15174 s i matched, reference_jump_imm_jal_not_v15180 s i matched, reference_jump_imm_jal_not_v15186 s i matched, reference_jump_imm_jal_not_v15192 s i matched, reference_jump_imm_jal_not_v15199 s i matched, reference_jump_imm_jal_not_v15206 s i matched, reference_jump_imm_jal_not_v15213 s i matched, reference_jump_imm_jal_not_v15220 s i matched, reference_jump_imm_jal_not_v15227 s i matched, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [BitVec.getLsbD_extractLsb']
  by_cases small : k < 5
  · have b12 : 7 + k < 12 := by omega
    have b15 : 7 + k < 15 := by omega
    have b20 : 7 + k < 20 := by omega
    have b21 : 7 + k < 21 := by omega
    have b31 : 7 + k < 31 := by omega
    simp [small, b12, b15, b20, b21, b31]
  · simp [small]

theorem reference_jump_jalr_destination (s : State) (i : Inputs)
    (commit : v9 s i = 1)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 103) :
    v15142 s i = BitVec.extractLsb' 7 5 (v14575 s i) := by
  have hit : v14901 s i = 1 := by simp [v14901, v14898, v14900, v14899, matched]
  simp only [v15142, v14560, v14559, v14558, v15141, v15140, v15139, v15138, v15137, v15136, v15135, v15134, v15133, v15132, v15131, v15130, v15129, v15128, v15127, v15126, v15125, v15124, v15123, v15122, v15121, v15120, v15119, v15118, v15117, v15116, v15115, v15114, v15113, v15112, v15111, v15110, v15109, v15108, v15107, v15106, v15105, v15104, v15103, v15102, v15101, v15100, v15099, v14905, v14904, v14903, v14902, v15076, commit, hit, reference_jump_imm_jalr_not_v14578 s i matched, reference_jump_imm_jalr_not_v14583 s i matched, reference_jump_imm_jalr_not_v14589 s i matched, reference_jump_imm_jalr_not_v14595 s i matched, reference_jump_imm_jalr_not_v14601 s i matched, reference_jump_imm_jalr_not_v14613 s i matched, reference_jump_imm_jalr_not_v14621 s i matched, reference_jump_imm_jalr_not_v14629 s i matched, reference_jump_imm_jalr_not_v14637 s i matched, reference_jump_imm_jalr_not_v14645 s i matched, reference_jump_imm_jalr_not_v14653 s i matched, reference_jump_imm_jalr_not_v14661 s i matched, reference_jump_imm_jalr_not_v14669 s i matched, reference_jump_imm_jalr_not_v14677 s i matched, reference_jump_imm_jalr_not_v14685 s i matched, reference_jump_imm_jalr_not_v14693 s i matched, reference_jump_imm_jalr_not_v14701 s i matched, reference_jump_imm_jalr_not_v14710 s i matched, reference_jump_imm_jalr_not_v14718 s i matched, reference_jump_imm_jalr_not_v14725 s i matched, reference_jump_imm_jalr_not_v14733 s i matched, reference_jump_imm_jalr_not_v14741 s i matched, reference_jump_imm_jalr_not_v14749 s i matched, reference_jump_imm_jalr_not_v14757 s i matched, reference_jump_imm_jalr_not_v14765 s i matched, reference_jump_imm_jalr_not_v14773 s i matched, reference_jump_imm_jalr_not_v14781 s i matched, reference_jump_imm_jalr_not_v14789 s i matched, reference_jump_imm_jalr_not_v14796 s i matched, reference_jump_imm_jalr_not_v14803 s i matched, reference_jump_imm_jalr_not_v14811 s i matched, reference_jump_imm_jalr_not_v14818 s i matched, reference_jump_imm_jalr_not_v14825 s i matched, reference_jump_imm_jalr_not_v14833 s i matched, reference_jump_imm_jalr_not_v14841 s i matched, reference_jump_imm_jalr_not_v14847 s i matched, reference_jump_imm_jalr_not_v14853 s i matched, reference_jump_imm_jalr_not_v14861 s i matched, reference_jump_imm_jalr_not_v14869 s i matched, reference_jump_imm_jalr_not_v14877 s i matched, reference_jump_imm_jalr_not_v14885 s i matched, reference_jump_imm_jalr_not_v14893 s i matched, reference_jump_imm_jalr_not_v14909 s i matched, reference_jump_imm_jalr_not_v14917 s i matched, reference_jump_imm_jalr_not_v14925 s i matched, reference_jump_imm_jalr_not_v14933 s i matched, reference_jump_imm_jalr_not_v14941 s i matched, reference_jump_imm_jalr_not_v14949 s i matched, reference_jump_imm_jalr_not_v14957 s i matched, reference_jump_imm_jalr_not_v14965 s i matched, reference_jump_imm_jalr_not_v14973 s i matched, reference_jump_imm_jalr_not_v14981 s i matched, reference_jump_imm_jalr_not_v14989 s i matched, reference_jump_imm_jalr_not_v14998 s i matched, reference_jump_imm_jalr_not_v15004 s i matched, reference_jump_imm_jalr_not_v15009 s i matched, reference_jump_imm_jalr_not_v15016 s i matched, reference_jump_imm_jalr_not_v15023 s i matched, reference_jump_imm_jalr_not_v15031 s i matched, reference_jump_imm_jalr_not_v15039 s i matched, reference_jump_imm_jalr_not_v15047 s i matched, reference_jump_imm_jalr_not_v15055 s i matched, reference_jump_imm_jalr_not_v15063 s i matched, reference_jump_imm_jalr_not_v15071 s i matched, reference_jump_imm_jalr_not_v15160 s i matched, reference_jump_imm_jalr_not_v15174 s i matched, reference_jump_imm_jalr_not_v15180 s i matched, reference_jump_imm_jalr_not_v15186 s i matched, reference_jump_imm_jalr_not_v15192 s i matched, reference_jump_imm_jalr_not_v15199 s i matched, reference_jump_imm_jalr_not_v15206 s i matched, reference_jump_imm_jalr_not_v15213 s i matched, reference_jump_imm_jalr_not_v15220 s i matched, reference_jump_imm_jalr_not_v15227 s i matched, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [BitVec.getLsbD_extractLsb']
  by_cases small : k < 5
  · have b12 : 7 + k < 12 := by omega
    have b15 : 7 + k < 15 := by omega
    have b20 : 7 + k < 20 := by omega
    have b21 : 7 + k < 21 := by omega
    have b31 : 7 + k < 31 := by omega
    simp [small, b12, b15, b20, b21, b31]
  · simp [small]

theorem reference_jump_destination (s : State) (i : Inputs) (operation : JumpOp)
    (commit : v9 s i = 1)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    v15142 s i = BitVec.extractLsb' 7 5 (v14575 s i) := by
  cases operation with
  | jal => exact reference_jump_jal_destination s i commit matched
  | jalr => exact reference_jump_jalr_destination s i commit matched
#print axioms reference_jump_destination
end NutShellProofs
