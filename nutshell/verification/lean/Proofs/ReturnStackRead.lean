import Proofs.ReturnStackAlignment
namespace NutShellProofs
open nNutCore
theorem return_stack_read_aligned (s : State) (i : Inputs) (slots : ReturnStackAligned s) :
    BitVec.extractLsb' 0 2 (v8376 s i) = 0 := by
  rcases slots with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩
  have bound := s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.isLt
  have cases : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 0 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 1 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 2 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 3 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 4 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 5 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 6 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 7 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 8 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 9 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 10 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 11 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 12 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 13 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 14 ∨ s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue.toNat = 15 := by omega
  rcases cases with c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (0 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h0
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (1 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h1
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (2 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h2
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (3 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h3
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (4 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h4
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (5 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h5
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (6 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h6
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (7 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h7
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (8 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h8
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (9 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h9
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (10 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h10
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (11 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h11
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (12 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h12
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (13 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h13
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (14 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h14
  · have ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = (15 : BitVec 4) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, v8361, v8360, v8359, v8358, v110, ptr] using h15

/-- Capturing a stack read establishes alignment without any assumption on the
unreset old rasTarget register. -/
theorem return_target_capture_aligned (s : State) (i : Inputs)
    (slots : ReturnStackAligned s) (capture : v2701 s i = 1) :
    BitVec.extractLsb' 0 2 (step s i).g32.r1054_nfrontend_5Fifu_5Fbp1_5FrasTarget = 0 := by
  change BitVec.extractLsb' 0 2 (v8377 s i) = 0
  rw [v8377, if_pos capture]
  exact return_stack_read_aligned s i slots

theorem return_target_alignment_hold (s : State) (i : Inputs)
    (old : BitVec.extractLsb' 0 2 s.g32.r1054_nfrontend_5Fifu_5Fbp1_5FrasTarget = 0)
    (slots : ReturnStackAligned s) :
    BitVec.extractLsb' 0 2 (step s i).g32.r1054_nfrontend_5Fifu_5Fbp1_5FrasTarget = 0 := by
  by_cases capture : v2701 s i = 1
  · exact return_target_capture_aligned s i slots capture
  · change BitVec.extractLsb' 0 2 (v8377 s i) = 0
    simpa only [v8377, if_neg capture] using old
#print axioms return_stack_read_aligned
#print axioms return_target_capture_aligned
#print axioms return_target_alignment_hold
end NutShellProofs
