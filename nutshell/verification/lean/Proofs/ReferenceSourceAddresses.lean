import Proofs.PipelineCapture
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
-- Reference read port numbering is reversed relative to DUT source numbering.
private theorem source_select (p : Prop) [Decidable p] (a b : Bool) (x : BitVec 5) :
    (if (if p then a else b) then x else 0) =
      (if p then (if a then x else 0) else (if b then x else 0)) := by
  by_cases h : p <;> simp [h]

private theorem source_extract_low (x : BitVec n) (start len keep : Nat)
    (bound : start + len ≤ keep) :
    BitVec.extractLsb' start len (BitVec.extractLsb' 0 keep x) =
      BitVec.extractLsb' start len x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [BitVec.getLsbD_extractLsb']
  by_cases h : k < len
  · have hk : start + k < keep := by omega
    simp [h, hk]
  · simp [h]


private def refRs1_v15397 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15397_eq (s : State) (i : Inputs) :
    v15397 s i = if refRs1_v15397 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15397, v15397, v14584, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15398 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15398_eq (s : State) (i : Inputs) :
    v15398 s i = if refRs1_v15398 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15398, v15398, v14590, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15399 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15399_eq (s : State) (i : Inputs) :
    v15399 s i = if refRs1_v15399 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15399, v15399, v14596, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15400 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15400_eq (s : State) (i : Inputs) :
    v15400 s i = if refRs1_v15400 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15400, v15400, v14602, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15401 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15401_eq (s : State) (i : Inputs) :
    v15401 s i = if refRs1_v15401 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15401, v15401, v14607, v14606, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15402 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15402_eq (s : State) (i : Inputs) :
    v15402 s i = if refRs1_v15402 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15402, v15402, v14615, v14614, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15403 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15403_eq (s : State) (i : Inputs) :
    v15403 s i = if refRs1_v15403 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15403, v15403, v14623, v14622, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15404 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15404_eq (s : State) (i : Inputs) :
    v15404 s i = if refRs1_v15404 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15404, v15404, v14631, v14630, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15405 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15405_eq (s : State) (i : Inputs) :
    v15405 s i = if refRs1_v15405 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15405, v15405, v14639, v14638, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15406 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15406_eq (s : State) (i : Inputs) :
    v15406 s i = if refRs1_v15406 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15406, v15406, v14647, v14646, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15407 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15407_eq (s : State) (i : Inputs) :
    v15407 s i = if refRs1_v15407 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15407, v15407, v14655, v14654, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15408 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15408_eq (s : State) (i : Inputs) :
    v15408 s i = if refRs1_v15408 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15408, v15408, v14663, v14662, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15409 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15409_eq (s : State) (i : Inputs) :
    v15409 s i = if refRs1_v15409 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15409, v15409, v14671, v14670, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15410 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15410_eq (s : State) (i : Inputs) :
    v15410 s i = if refRs1_v15410 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15410, v15410, v14679, v14678, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15411 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15411_eq (s : State) (i : Inputs) :
    v15411 s i = if refRs1_v15411 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15411, v15411, v14687, v14686, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15412 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15412_eq (s : State) (i : Inputs) :
    v15412 s i = if refRs1_v15412 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15412, v15412, v14695, v14694, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15413 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15413_eq (s : State) (i : Inputs) :
    v15413 s i = if refRs1_v15413 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15413, v15413, v14703, v14702, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15415 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15415_eq (s : State) (i : Inputs) :
    v15415 s i = if refRs1_v15415 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15415, v15415, v15414, v15161, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15416 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15416_eq (s : State) (i : Inputs) :
    v15416 s i = if refRs1_v15416 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15416, v15416, v14711, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15417 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15417_eq (s : State) (i : Inputs) :
    v15417 s i = if refRs1_v15417 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15417, v15417, v14719, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15418 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15418_eq (s : State) (i : Inputs) :
    v15418 s i = if refRs1_v15418 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15418, v15418, v14727, v14726, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15419 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15419_eq (s : State) (i : Inputs) :
    v15419 s i = if refRs1_v15419 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15419, v15419, v14735, v14734, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15420 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15420_eq (s : State) (i : Inputs) :
    v15420 s i = if refRs1_v15420 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15420, v15420, v14743, v14742, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15421 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15421_eq (s : State) (i : Inputs) :
    v15421 s i = if refRs1_v15421 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15421, v15421, v14751, v14750, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15422 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15422_eq (s : State) (i : Inputs) :
    v15422 s i = if refRs1_v15422 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15422, v15422, v14759, v14758, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15423 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15423_eq (s : State) (i : Inputs) :
    v15423 s i = if refRs1_v15423 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15423, v15423, v14767, v14766, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15424 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15424_eq (s : State) (i : Inputs) :
    v15424 s i = if refRs1_v15424 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15424, v15424, v14775, v14774, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15425 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15425_eq (s : State) (i : Inputs) :
    v15425 s i = if refRs1_v15425 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15425, v15425, v14783, v14782, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15426 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15426_eq (s : State) (i : Inputs) :
    v15426 s i = if refRs1_v15426 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15426, v15426, v14790, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15427 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15427_eq (s : State) (i : Inputs) :
    v15427 s i = if refRs1_v15427 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15427, v15427, v14797, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15428 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15428_eq (s : State) (i : Inputs) :
    v15428 s i = if refRs1_v15428 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15428, v15428, v14804, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15429 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15429_eq (s : State) (i : Inputs) :
    v15429 s i = if refRs1_v15429 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15429, v15429, v14812, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15430 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15430_eq (s : State) (i : Inputs) :
    v15430 s i = if refRs1_v15430 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15430, v15430, v14819, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15431 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15431_eq (s : State) (i : Inputs) :
    v15431 s i = if refRs1_v15431 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15431, v15431, v14826, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15432 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15432_eq (s : State) (i : Inputs) :
    v15432 s i = if refRs1_v15432 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15432, v15432, v14834, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15433 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15433_eq (s : State) (i : Inputs) :
    v15433 s i = if refRs1_v15433 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15433, v15433, v14842, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15434 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15434_eq (s : State) (i : Inputs) :
    v15434 s i = if refRs1_v15434 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15434, v15434, v14848, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15435 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15435_eq (s : State) (i : Inputs) :
    v15435 s i = if refRs1_v15435 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15435, v15435, v14854, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15437 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15437_eq (s : State) (i : Inputs) :
    v15437 s i = if refRs1_v15437 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15437, v15437, v15436, v15175, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15439 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15439_eq (s : State) (i : Inputs) :
    v15439 s i = if refRs1_v15439 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15439, v15439, v15438, v15181, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15441 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15441_eq (s : State) (i : Inputs) :
    v15441 s i = if refRs1_v15441 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15441, v15441, v15440, v15187, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15442 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15442_eq (s : State) (i : Inputs) :
    v15442 s i = if refRs1_v15442 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15442, v15442, v14862, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15443 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15443_eq (s : State) (i : Inputs) :
    v15443 s i = if refRs1_v15443 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15443, v15443, v14870, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15444 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15444_eq (s : State) (i : Inputs) :
    v15444 s i = if refRs1_v15444 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15444, v15444, v14878, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15445 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15445_eq (s : State) (i : Inputs) :
    v15445 s i = if refRs1_v15445 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15445, v15445, v14886, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15446 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15446_eq (s : State) (i : Inputs) :
    v15446 s i = if refRs1_v15446 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15446, v15446, v14894, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15448 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15448_eq (s : State) (i : Inputs) :
    v15448 s i = if refRs1_v15448 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15448, v15448, v15447, v15194, v15193, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15450 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15450_eq (s : State) (i : Inputs) :
    v15450 s i = if refRs1_v15450 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15450, v15450, v15449, v15201, v15200, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15452 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15452_eq (s : State) (i : Inputs) :
    v15452 s i = if refRs1_v15452 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15452, v15452, v15451, v15208, v15207, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15454 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15454_eq (s : State) (i : Inputs) :
    v15454 s i = if refRs1_v15454 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15454, v15454, v15453, v15215, v15214, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15456 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15456_eq (s : State) (i : Inputs) :
    v15456 s i = if refRs1_v15456 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15456, v15456, v15455, v15222, v15221, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15458 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15458_eq (s : State) (i : Inputs) :
    v15458 s i = if refRs1_v15458 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15458, v15458, v15457, v15229, v15228, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15459 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15459_eq (s : State) (i : Inputs) :
    v15459 s i = if refRs1_v15459 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15459, v15459, v14902, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15460 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15460_eq (s : State) (i : Inputs) :
    v15460 s i = if refRs1_v15460 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15460, v15460, v14919, v14918, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15461 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15461_eq (s : State) (i : Inputs) :
    v15461 s i = if refRs1_v15461 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15461, v15461, v14927, v14926, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15462 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15462_eq (s : State) (i : Inputs) :
    v15462 s i = if refRs1_v15462 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15462, v15462, v14935, v14934, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15463 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15463_eq (s : State) (i : Inputs) :
    v15463 s i = if refRs1_v15463 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15463, v15463, v14943, v14942, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15464 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15464_eq (s : State) (i : Inputs) :
    v15464 s i = if refRs1_v15464 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15464, v15464, v14951, v14950, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15465 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15465_eq (s : State) (i : Inputs) :
    v15465 s i = if refRs1_v15465 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15465, v15465, v14959, v14958, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15466 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15466_eq (s : State) (i : Inputs) :
    v15466 s i = if refRs1_v15466 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15466, v15466, v14967, v14966, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15467 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15467_eq (s : State) (i : Inputs) :
    v15467 s i = if refRs1_v15467 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15467, v15467, v14975, v14974, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15468 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15468_eq (s : State) (i : Inputs) :
    v15468 s i = if refRs1_v15468 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15468, v15468, v14983, v14982, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15469 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15469_eq (s : State) (i : Inputs) :
    v15469 s i = if refRs1_v15469 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15469, v15469, v14991, v14990, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15470 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15470_eq (s : State) (i : Inputs) :
    v15470 s i = if refRs1_v15470 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15470, v15470, v15010, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15471 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15471_eq (s : State) (i : Inputs) :
    v15471 s i = if refRs1_v15471 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15471, v15471, v15017, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15472 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15472_eq (s : State) (i : Inputs) :
    v15472 s i = if refRs1_v15472 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15472, v15472, v15024, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15473 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15473_eq (s : State) (i : Inputs) :
    v15473 s i = if refRs1_v15473 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15473, v15473, v15032, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15474 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15474_eq (s : State) (i : Inputs) :
    v15474 s i = if refRs1_v15474 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15474, v15474, v15040, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15475 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15475_eq (s : State) (i : Inputs) :
    v15475 s i = if refRs1_v15475 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15475, v15475, v15048, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15476 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15476_eq (s : State) (i : Inputs) :
    v15476 s i = if refRs1_v15476 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15476, v15476, v15056, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15477 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15477_eq (s : State) (i : Inputs) :
    v15477 s i = if refRs1_v15477 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15477, v15477, v15064, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15478 (s : State) (i : Inputs) : Bool := true
private theorem refRs1_v15478_eq (s : State) (i : Inputs) :
    v15478 s i = if refRs1_v15478 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15478, v15478, v15072, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15076 (s : State) (i : Inputs) : Bool := false
private theorem refRs1_v15076_eq (s : State) (i : Inputs) :
    v15076 s i = if refRs1_v15076 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs1_v15076, v15076, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs1_v15479 (s : State) (i : Inputs) : Bool := if v15071 s i = 1 then refRs1_v15478 s i else refRs1_v15076 s i
private theorem refRs1_v15479_eq (s : State) (i : Inputs) :
    v15479 s i = if refRs1_v15479 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15479, refRs1_v15478_eq, refRs1_v15076_eq]
  simp only [refRs1_v15479, source_select]
  all_goals rfl

private def refRs1_v15480 (s : State) (i : Inputs) : Bool := if v15063 s i = 1 then refRs1_v15477 s i else refRs1_v15479 s i
private theorem refRs1_v15480_eq (s : State) (i : Inputs) :
    v15480 s i = if refRs1_v15480 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15480, refRs1_v15477_eq, refRs1_v15479_eq]
  simp only [refRs1_v15480, source_select]
  all_goals rfl

private def refRs1_v15481 (s : State) (i : Inputs) : Bool := if v15055 s i = 1 then refRs1_v15476 s i else refRs1_v15480 s i
private theorem refRs1_v15481_eq (s : State) (i : Inputs) :
    v15481 s i = if refRs1_v15481 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15481, refRs1_v15476_eq, refRs1_v15480_eq]
  simp only [refRs1_v15481, source_select]
  all_goals rfl

private def refRs1_v15482 (s : State) (i : Inputs) : Bool := if v15047 s i = 1 then refRs1_v15475 s i else refRs1_v15481 s i
private theorem refRs1_v15482_eq (s : State) (i : Inputs) :
    v15482 s i = if refRs1_v15482 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15482, refRs1_v15475_eq, refRs1_v15481_eq]
  simp only [refRs1_v15482, source_select]
  all_goals rfl

private def refRs1_v15483 (s : State) (i : Inputs) : Bool := if v15039 s i = 1 then refRs1_v15474 s i else refRs1_v15482 s i
private theorem refRs1_v15483_eq (s : State) (i : Inputs) :
    v15483 s i = if refRs1_v15483 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15483, refRs1_v15474_eq, refRs1_v15482_eq]
  simp only [refRs1_v15483, source_select]
  all_goals rfl

private def refRs1_v15484 (s : State) (i : Inputs) : Bool := if v15031 s i = 1 then refRs1_v15473 s i else refRs1_v15483 s i
private theorem refRs1_v15484_eq (s : State) (i : Inputs) :
    v15484 s i = if refRs1_v15484 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15484, refRs1_v15473_eq, refRs1_v15483_eq]
  simp only [refRs1_v15484, source_select]
  all_goals rfl

private def refRs1_v15485 (s : State) (i : Inputs) : Bool := if v15023 s i = 1 then refRs1_v15472 s i else refRs1_v15484 s i
private theorem refRs1_v15485_eq (s : State) (i : Inputs) :
    v15485 s i = if refRs1_v15485 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15485, refRs1_v15472_eq, refRs1_v15484_eq]
  simp only [refRs1_v15485, source_select]
  all_goals rfl

private def refRs1_v15486 (s : State) (i : Inputs) : Bool := if v15016 s i = 1 then refRs1_v15471 s i else refRs1_v15485 s i
private theorem refRs1_v15486_eq (s : State) (i : Inputs) :
    v15486 s i = if refRs1_v15486 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15486, refRs1_v15471_eq, refRs1_v15485_eq]
  simp only [refRs1_v15486, source_select]
  all_goals rfl

private def refRs1_v15487 (s : State) (i : Inputs) : Bool := if v15009 s i = 1 then refRs1_v15470 s i else refRs1_v15486 s i
private theorem refRs1_v15487_eq (s : State) (i : Inputs) :
    v15487 s i = if refRs1_v15487 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15487, refRs1_v15470_eq, refRs1_v15486_eq]
  simp only [refRs1_v15487, source_select]
  all_goals rfl

private def refRs1_v15488 (s : State) (i : Inputs) : Bool := if v14989 s i = 1 then refRs1_v15469 s i else refRs1_v15487 s i
private theorem refRs1_v15488_eq (s : State) (i : Inputs) :
    v15488 s i = if refRs1_v15488 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15488, refRs1_v15469_eq, refRs1_v15487_eq]
  simp only [refRs1_v15488, source_select]
  all_goals rfl

private def refRs1_v15489 (s : State) (i : Inputs) : Bool := if v14981 s i = 1 then refRs1_v15468 s i else refRs1_v15488 s i
private theorem refRs1_v15489_eq (s : State) (i : Inputs) :
    v15489 s i = if refRs1_v15489 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15489, refRs1_v15468_eq, refRs1_v15488_eq]
  simp only [refRs1_v15489, source_select]
  all_goals rfl

private def refRs1_v15490 (s : State) (i : Inputs) : Bool := if v14973 s i = 1 then refRs1_v15467 s i else refRs1_v15489 s i
private theorem refRs1_v15490_eq (s : State) (i : Inputs) :
    v15490 s i = if refRs1_v15490 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15490, refRs1_v15467_eq, refRs1_v15489_eq]
  simp only [refRs1_v15490, source_select]
  all_goals rfl

private def refRs1_v15491 (s : State) (i : Inputs) : Bool := if v14965 s i = 1 then refRs1_v15466 s i else refRs1_v15490 s i
private theorem refRs1_v15491_eq (s : State) (i : Inputs) :
    v15491 s i = if refRs1_v15491 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15491, refRs1_v15466_eq, refRs1_v15490_eq]
  simp only [refRs1_v15491, source_select]
  all_goals rfl

private def refRs1_v15492 (s : State) (i : Inputs) : Bool := if v14957 s i = 1 then refRs1_v15465 s i else refRs1_v15491 s i
private theorem refRs1_v15492_eq (s : State) (i : Inputs) :
    v15492 s i = if refRs1_v15492 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15492, refRs1_v15465_eq, refRs1_v15491_eq]
  simp only [refRs1_v15492, source_select]
  all_goals rfl

private def refRs1_v15493 (s : State) (i : Inputs) : Bool := if v14949 s i = 1 then refRs1_v15464 s i else refRs1_v15492 s i
private theorem refRs1_v15493_eq (s : State) (i : Inputs) :
    v15493 s i = if refRs1_v15493 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15493, refRs1_v15464_eq, refRs1_v15492_eq]
  simp only [refRs1_v15493, source_select]
  all_goals rfl

private def refRs1_v15494 (s : State) (i : Inputs) : Bool := if v14941 s i = 1 then refRs1_v15463 s i else refRs1_v15493 s i
private theorem refRs1_v15494_eq (s : State) (i : Inputs) :
    v15494 s i = if refRs1_v15494 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15494, refRs1_v15463_eq, refRs1_v15493_eq]
  simp only [refRs1_v15494, source_select]
  all_goals rfl

private def refRs1_v15495 (s : State) (i : Inputs) : Bool := if v14933 s i = 1 then refRs1_v15462 s i else refRs1_v15494 s i
private theorem refRs1_v15495_eq (s : State) (i : Inputs) :
    v15495 s i = if refRs1_v15495 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15495, refRs1_v15462_eq, refRs1_v15494_eq]
  simp only [refRs1_v15495, source_select]
  all_goals rfl

private def refRs1_v15496 (s : State) (i : Inputs) : Bool := if v14925 s i = 1 then refRs1_v15461 s i else refRs1_v15495 s i
private theorem refRs1_v15496_eq (s : State) (i : Inputs) :
    v15496 s i = if refRs1_v15496 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15496, refRs1_v15461_eq, refRs1_v15495_eq]
  simp only [refRs1_v15496, source_select]
  all_goals rfl

private def refRs1_v15497 (s : State) (i : Inputs) : Bool := if v14917 s i = 1 then refRs1_v15460 s i else refRs1_v15496 s i
private theorem refRs1_v15497_eq (s : State) (i : Inputs) :
    v15497 s i = if refRs1_v15497 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15497, refRs1_v15460_eq, refRs1_v15496_eq]
  simp only [refRs1_v15497, source_select]
  all_goals rfl

private def refRs1_v15498 (s : State) (i : Inputs) : Bool := if v14901 s i = 1 then refRs1_v15459 s i else refRs1_v15497 s i
private theorem refRs1_v15498_eq (s : State) (i : Inputs) :
    v15498 s i = if refRs1_v15498 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15498, refRs1_v15459_eq, refRs1_v15497_eq]
  simp only [refRs1_v15498, source_select]
  all_goals rfl

private def refRs1_v15499 (s : State) (i : Inputs) : Bool := if v15227 s i = 1 then refRs1_v15458 s i else refRs1_v15498 s i
private theorem refRs1_v15499_eq (s : State) (i : Inputs) :
    v15499 s i = if refRs1_v15499 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15499, refRs1_v15458_eq, refRs1_v15498_eq]
  simp only [refRs1_v15499, source_select]
  all_goals rfl

private def refRs1_v15500 (s : State) (i : Inputs) : Bool := if v15220 s i = 1 then refRs1_v15456 s i else refRs1_v15499 s i
private theorem refRs1_v15500_eq (s : State) (i : Inputs) :
    v15500 s i = if refRs1_v15500 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15500, refRs1_v15456_eq, refRs1_v15499_eq]
  simp only [refRs1_v15500, source_select]
  all_goals rfl

private def refRs1_v15501 (s : State) (i : Inputs) : Bool := if v15213 s i = 1 then refRs1_v15454 s i else refRs1_v15500 s i
private theorem refRs1_v15501_eq (s : State) (i : Inputs) :
    v15501 s i = if refRs1_v15501 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15501, refRs1_v15454_eq, refRs1_v15500_eq]
  simp only [refRs1_v15501, source_select]
  all_goals rfl

private def refRs1_v15502 (s : State) (i : Inputs) : Bool := if v15206 s i = 1 then refRs1_v15452 s i else refRs1_v15501 s i
private theorem refRs1_v15502_eq (s : State) (i : Inputs) :
    v15502 s i = if refRs1_v15502 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15502, refRs1_v15452_eq, refRs1_v15501_eq]
  simp only [refRs1_v15502, source_select]
  all_goals rfl

private def refRs1_v15503 (s : State) (i : Inputs) : Bool := if v15199 s i = 1 then refRs1_v15450 s i else refRs1_v15502 s i
private theorem refRs1_v15503_eq (s : State) (i : Inputs) :
    v15503 s i = if refRs1_v15503 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15503, refRs1_v15450_eq, refRs1_v15502_eq]
  simp only [refRs1_v15503, source_select]
  all_goals rfl

private def refRs1_v15504 (s : State) (i : Inputs) : Bool := if v15192 s i = 1 then refRs1_v15448 s i else refRs1_v15503 s i
private theorem refRs1_v15504_eq (s : State) (i : Inputs) :
    v15504 s i = if refRs1_v15504 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15504, refRs1_v15448_eq, refRs1_v15503_eq]
  simp only [refRs1_v15504, source_select]
  all_goals rfl

private def refRs1_v15505 (s : State) (i : Inputs) : Bool := if v14893 s i = 1 then refRs1_v15446 s i else refRs1_v15504 s i
private theorem refRs1_v15505_eq (s : State) (i : Inputs) :
    v15505 s i = if refRs1_v15505 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15505, refRs1_v15446_eq, refRs1_v15504_eq]
  simp only [refRs1_v15505, source_select]
  all_goals rfl

private def refRs1_v15506 (s : State) (i : Inputs) : Bool := if v14885 s i = 1 then refRs1_v15445 s i else refRs1_v15505 s i
private theorem refRs1_v15506_eq (s : State) (i : Inputs) :
    v15506 s i = if refRs1_v15506 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15506, refRs1_v15445_eq, refRs1_v15505_eq]
  simp only [refRs1_v15506, source_select]
  all_goals rfl

private def refRs1_v15507 (s : State) (i : Inputs) : Bool := if v14877 s i = 1 then refRs1_v15444 s i else refRs1_v15506 s i
private theorem refRs1_v15507_eq (s : State) (i : Inputs) :
    v15507 s i = if refRs1_v15507 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15507, refRs1_v15444_eq, refRs1_v15506_eq]
  simp only [refRs1_v15507, source_select]
  all_goals rfl

private def refRs1_v15508 (s : State) (i : Inputs) : Bool := if v14869 s i = 1 then refRs1_v15443 s i else refRs1_v15507 s i
private theorem refRs1_v15508_eq (s : State) (i : Inputs) :
    v15508 s i = if refRs1_v15508 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15508, refRs1_v15443_eq, refRs1_v15507_eq]
  simp only [refRs1_v15508, source_select]
  all_goals rfl

private def refRs1_v15509 (s : State) (i : Inputs) : Bool := if v14861 s i = 1 then refRs1_v15442 s i else refRs1_v15508 s i
private theorem refRs1_v15509_eq (s : State) (i : Inputs) :
    v15509 s i = if refRs1_v15509 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15509, refRs1_v15442_eq, refRs1_v15508_eq]
  simp only [refRs1_v15509, source_select]
  all_goals rfl

private def refRs1_v15510 (s : State) (i : Inputs) : Bool := if v15186 s i = 1 then refRs1_v15441 s i else refRs1_v15509 s i
private theorem refRs1_v15510_eq (s : State) (i : Inputs) :
    v15510 s i = if refRs1_v15510 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15510, refRs1_v15441_eq, refRs1_v15509_eq]
  simp only [refRs1_v15510, source_select]
  all_goals rfl

private def refRs1_v15511 (s : State) (i : Inputs) : Bool := if v15180 s i = 1 then refRs1_v15439 s i else refRs1_v15510 s i
private theorem refRs1_v15511_eq (s : State) (i : Inputs) :
    v15511 s i = if refRs1_v15511 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15511, refRs1_v15439_eq, refRs1_v15510_eq]
  simp only [refRs1_v15511, source_select]
  all_goals rfl

private def refRs1_v15512 (s : State) (i : Inputs) : Bool := if v15174 s i = 1 then refRs1_v15437 s i else refRs1_v15511 s i
private theorem refRs1_v15512_eq (s : State) (i : Inputs) :
    v15512 s i = if refRs1_v15512 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15512, refRs1_v15437_eq, refRs1_v15511_eq]
  simp only [refRs1_v15512, source_select]
  all_goals rfl

private def refRs1_v15513 (s : State) (i : Inputs) : Bool := if v14853 s i = 1 then refRs1_v15435 s i else refRs1_v15512 s i
private theorem refRs1_v15513_eq (s : State) (i : Inputs) :
    v15513 s i = if refRs1_v15513 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15513, refRs1_v15435_eq, refRs1_v15512_eq]
  simp only [refRs1_v15513, source_select]
  all_goals rfl

private def refRs1_v15514 (s : State) (i : Inputs) : Bool := if v14847 s i = 1 then refRs1_v15434 s i else refRs1_v15513 s i
private theorem refRs1_v15514_eq (s : State) (i : Inputs) :
    v15514 s i = if refRs1_v15514 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15514, refRs1_v15434_eq, refRs1_v15513_eq]
  simp only [refRs1_v15514, source_select]
  all_goals rfl

private def refRs1_v15515 (s : State) (i : Inputs) : Bool := if v14841 s i = 1 then refRs1_v15433 s i else refRs1_v15514 s i
private theorem refRs1_v15515_eq (s : State) (i : Inputs) :
    v15515 s i = if refRs1_v15515 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15515, refRs1_v15433_eq, refRs1_v15514_eq]
  simp only [refRs1_v15515, source_select]
  all_goals rfl

private def refRs1_v15516 (s : State) (i : Inputs) : Bool := if v14833 s i = 1 then refRs1_v15432 s i else refRs1_v15515 s i
private theorem refRs1_v15516_eq (s : State) (i : Inputs) :
    v15516 s i = if refRs1_v15516 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15516, refRs1_v15432_eq, refRs1_v15515_eq]
  simp only [refRs1_v15516, source_select]
  all_goals rfl

private def refRs1_v15517 (s : State) (i : Inputs) : Bool := if v14825 s i = 1 then refRs1_v15431 s i else refRs1_v15516 s i
private theorem refRs1_v15517_eq (s : State) (i : Inputs) :
    v15517 s i = if refRs1_v15517 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15517, refRs1_v15431_eq, refRs1_v15516_eq]
  simp only [refRs1_v15517, source_select]
  all_goals rfl

private def refRs1_v15518 (s : State) (i : Inputs) : Bool := if v14818 s i = 1 then refRs1_v15430 s i else refRs1_v15517 s i
private theorem refRs1_v15518_eq (s : State) (i : Inputs) :
    v15518 s i = if refRs1_v15518 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15518, refRs1_v15430_eq, refRs1_v15517_eq]
  simp only [refRs1_v15518, source_select]
  all_goals rfl

private def refRs1_v15519 (s : State) (i : Inputs) : Bool := if v14811 s i = 1 then refRs1_v15429 s i else refRs1_v15518 s i
private theorem refRs1_v15519_eq (s : State) (i : Inputs) :
    v15519 s i = if refRs1_v15519 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15519, refRs1_v15429_eq, refRs1_v15518_eq]
  simp only [refRs1_v15519, source_select]
  all_goals rfl

private def refRs1_v15520 (s : State) (i : Inputs) : Bool := if v14803 s i = 1 then refRs1_v15428 s i else refRs1_v15519 s i
private theorem refRs1_v15520_eq (s : State) (i : Inputs) :
    v15520 s i = if refRs1_v15520 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15520, refRs1_v15428_eq, refRs1_v15519_eq]
  simp only [refRs1_v15520, source_select]
  all_goals rfl

private def refRs1_v15521 (s : State) (i : Inputs) : Bool := if v14796 s i = 1 then refRs1_v15427 s i else refRs1_v15520 s i
private theorem refRs1_v15521_eq (s : State) (i : Inputs) :
    v15521 s i = if refRs1_v15521 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15521, refRs1_v15427_eq, refRs1_v15520_eq]
  simp only [refRs1_v15521, source_select]
  all_goals rfl

private def refRs1_v15522 (s : State) (i : Inputs) : Bool := if v14789 s i = 1 then refRs1_v15426 s i else refRs1_v15521 s i
private theorem refRs1_v15522_eq (s : State) (i : Inputs) :
    v15522 s i = if refRs1_v15522 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15522, refRs1_v15426_eq, refRs1_v15521_eq]
  simp only [refRs1_v15522, source_select]
  all_goals rfl

private def refRs1_v15523 (s : State) (i : Inputs) : Bool := if v14781 s i = 1 then refRs1_v15425 s i else refRs1_v15522 s i
private theorem refRs1_v15523_eq (s : State) (i : Inputs) :
    v15523 s i = if refRs1_v15523 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15523, refRs1_v15425_eq, refRs1_v15522_eq]
  simp only [refRs1_v15523, source_select]
  all_goals rfl

private def refRs1_v15524 (s : State) (i : Inputs) : Bool := if v14773 s i = 1 then refRs1_v15424 s i else refRs1_v15523 s i
private theorem refRs1_v15524_eq (s : State) (i : Inputs) :
    v15524 s i = if refRs1_v15524 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15524, refRs1_v15424_eq, refRs1_v15523_eq]
  simp only [refRs1_v15524, source_select]
  all_goals rfl

private def refRs1_v15525 (s : State) (i : Inputs) : Bool := if v14765 s i = 1 then refRs1_v15423 s i else refRs1_v15524 s i
private theorem refRs1_v15525_eq (s : State) (i : Inputs) :
    v15525 s i = if refRs1_v15525 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15525, refRs1_v15423_eq, refRs1_v15524_eq]
  simp only [refRs1_v15525, source_select]
  all_goals rfl

private def refRs1_v15526 (s : State) (i : Inputs) : Bool := if v14757 s i = 1 then refRs1_v15422 s i else refRs1_v15525 s i
private theorem refRs1_v15526_eq (s : State) (i : Inputs) :
    v15526 s i = if refRs1_v15526 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15526, refRs1_v15422_eq, refRs1_v15525_eq]
  simp only [refRs1_v15526, source_select]
  all_goals rfl

private def refRs1_v15527 (s : State) (i : Inputs) : Bool := if v14749 s i = 1 then refRs1_v15421 s i else refRs1_v15526 s i
private theorem refRs1_v15527_eq (s : State) (i : Inputs) :
    v15527 s i = if refRs1_v15527 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15527, refRs1_v15421_eq, refRs1_v15526_eq]
  simp only [refRs1_v15527, source_select]
  all_goals rfl

private def refRs1_v15528 (s : State) (i : Inputs) : Bool := if v14741 s i = 1 then refRs1_v15420 s i else refRs1_v15527 s i
private theorem refRs1_v15528_eq (s : State) (i : Inputs) :
    v15528 s i = if refRs1_v15528 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15528, refRs1_v15420_eq, refRs1_v15527_eq]
  simp only [refRs1_v15528, source_select]
  all_goals rfl

private def refRs1_v15529 (s : State) (i : Inputs) : Bool := if v14733 s i = 1 then refRs1_v15419 s i else refRs1_v15528 s i
private theorem refRs1_v15529_eq (s : State) (i : Inputs) :
    v15529 s i = if refRs1_v15529 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15529, refRs1_v15419_eq, refRs1_v15528_eq]
  simp only [refRs1_v15529, source_select]
  all_goals rfl

private def refRs1_v15530 (s : State) (i : Inputs) : Bool := if v14725 s i = 1 then refRs1_v15418 s i else refRs1_v15529 s i
private theorem refRs1_v15530_eq (s : State) (i : Inputs) :
    v15530 s i = if refRs1_v15530 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15530, refRs1_v15418_eq, refRs1_v15529_eq]
  simp only [refRs1_v15530, source_select]
  all_goals rfl

private def refRs1_v15531 (s : State) (i : Inputs) : Bool := if v14718 s i = 1 then refRs1_v15417 s i else refRs1_v15530 s i
private theorem refRs1_v15531_eq (s : State) (i : Inputs) :
    v15531 s i = if refRs1_v15531 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15531, refRs1_v15417_eq, refRs1_v15530_eq]
  simp only [refRs1_v15531, source_select]
  all_goals rfl

private def refRs1_v15532 (s : State) (i : Inputs) : Bool := if v14710 s i = 1 then refRs1_v15416 s i else refRs1_v15531 s i
private theorem refRs1_v15532_eq (s : State) (i : Inputs) :
    v15532 s i = if refRs1_v15532 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15532, refRs1_v15416_eq, refRs1_v15531_eq]
  simp only [refRs1_v15532, source_select]
  all_goals rfl

private def refRs1_v15533 (s : State) (i : Inputs) : Bool := if v15160 s i = 1 then refRs1_v15415 s i else refRs1_v15532 s i
private theorem refRs1_v15533_eq (s : State) (i : Inputs) :
    v15533 s i = if refRs1_v15533 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15533, refRs1_v15415_eq, refRs1_v15532_eq]
  simp only [refRs1_v15533, source_select]
  all_goals rfl

private def refRs1_v15534 (s : State) (i : Inputs) : Bool := if v14701 s i = 1 then refRs1_v15413 s i else refRs1_v15533 s i
private theorem refRs1_v15534_eq (s : State) (i : Inputs) :
    v15534 s i = if refRs1_v15534 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15534, refRs1_v15413_eq, refRs1_v15533_eq]
  simp only [refRs1_v15534, source_select]
  all_goals rfl

private def refRs1_v15535 (s : State) (i : Inputs) : Bool := if v14693 s i = 1 then refRs1_v15412 s i else refRs1_v15534 s i
private theorem refRs1_v15535_eq (s : State) (i : Inputs) :
    v15535 s i = if refRs1_v15535 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15535, refRs1_v15412_eq, refRs1_v15534_eq]
  simp only [refRs1_v15535, source_select]
  all_goals rfl

private def refRs1_v15536 (s : State) (i : Inputs) : Bool := if v14685 s i = 1 then refRs1_v15411 s i else refRs1_v15535 s i
private theorem refRs1_v15536_eq (s : State) (i : Inputs) :
    v15536 s i = if refRs1_v15536 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15536, refRs1_v15411_eq, refRs1_v15535_eq]
  simp only [refRs1_v15536, source_select]
  all_goals rfl

private def refRs1_v15537 (s : State) (i : Inputs) : Bool := if v14677 s i = 1 then refRs1_v15410 s i else refRs1_v15536 s i
private theorem refRs1_v15537_eq (s : State) (i : Inputs) :
    v15537 s i = if refRs1_v15537 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15537, refRs1_v15410_eq, refRs1_v15536_eq]
  simp only [refRs1_v15537, source_select]
  all_goals rfl

private def refRs1_v15538 (s : State) (i : Inputs) : Bool := if v14669 s i = 1 then refRs1_v15409 s i else refRs1_v15537 s i
private theorem refRs1_v15538_eq (s : State) (i : Inputs) :
    v15538 s i = if refRs1_v15538 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15538, refRs1_v15409_eq, refRs1_v15537_eq]
  simp only [refRs1_v15538, source_select]
  all_goals rfl

private def refRs1_v15539 (s : State) (i : Inputs) : Bool := if v14661 s i = 1 then refRs1_v15408 s i else refRs1_v15538 s i
private theorem refRs1_v15539_eq (s : State) (i : Inputs) :
    v15539 s i = if refRs1_v15539 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15539, refRs1_v15408_eq, refRs1_v15538_eq]
  simp only [refRs1_v15539, source_select]
  all_goals rfl

private def refRs1_v15540 (s : State) (i : Inputs) : Bool := if v14653 s i = 1 then refRs1_v15407 s i else refRs1_v15539 s i
private theorem refRs1_v15540_eq (s : State) (i : Inputs) :
    v15540 s i = if refRs1_v15540 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15540, refRs1_v15407_eq, refRs1_v15539_eq]
  simp only [refRs1_v15540, source_select]
  all_goals rfl

private def refRs1_v15541 (s : State) (i : Inputs) : Bool := if v14645 s i = 1 then refRs1_v15406 s i else refRs1_v15540 s i
private theorem refRs1_v15541_eq (s : State) (i : Inputs) :
    v15541 s i = if refRs1_v15541 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15541, refRs1_v15406_eq, refRs1_v15540_eq]
  simp only [refRs1_v15541, source_select]
  all_goals rfl

private def refRs1_v15542 (s : State) (i : Inputs) : Bool := if v14637 s i = 1 then refRs1_v15405 s i else refRs1_v15541 s i
private theorem refRs1_v15542_eq (s : State) (i : Inputs) :
    v15542 s i = if refRs1_v15542 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15542, refRs1_v15405_eq, refRs1_v15541_eq]
  simp only [refRs1_v15542, source_select]
  all_goals rfl

private def refRs1_v15543 (s : State) (i : Inputs) : Bool := if v14629 s i = 1 then refRs1_v15404 s i else refRs1_v15542 s i
private theorem refRs1_v15543_eq (s : State) (i : Inputs) :
    v15543 s i = if refRs1_v15543 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15543, refRs1_v15404_eq, refRs1_v15542_eq]
  simp only [refRs1_v15543, source_select]
  all_goals rfl

private def refRs1_v15544 (s : State) (i : Inputs) : Bool := if v14621 s i = 1 then refRs1_v15403 s i else refRs1_v15543 s i
private theorem refRs1_v15544_eq (s : State) (i : Inputs) :
    v15544 s i = if refRs1_v15544 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15544, refRs1_v15403_eq, refRs1_v15543_eq]
  simp only [refRs1_v15544, source_select]
  all_goals rfl

private def refRs1_v15545 (s : State) (i : Inputs) : Bool := if v14613 s i = 1 then refRs1_v15402 s i else refRs1_v15544 s i
private theorem refRs1_v15545_eq (s : State) (i : Inputs) :
    v15545 s i = if refRs1_v15545 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15545, refRs1_v15402_eq, refRs1_v15544_eq]
  simp only [refRs1_v15545, source_select]
  all_goals rfl

private def refRs1_v15546 (s : State) (i : Inputs) : Bool := if v14578 s i = 1 then refRs1_v15401 s i else refRs1_v15545 s i
private theorem refRs1_v15546_eq (s : State) (i : Inputs) :
    v15546 s i = if refRs1_v15546 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15546, refRs1_v15401_eq, refRs1_v15545_eq]
  simp only [refRs1_v15546, source_select]
  all_goals rfl

private def refRs1_v15547 (s : State) (i : Inputs) : Bool := if v14601 s i = 1 then refRs1_v15400 s i else refRs1_v15546 s i
private theorem refRs1_v15547_eq (s : State) (i : Inputs) :
    v15547 s i = if refRs1_v15547 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15547, refRs1_v15400_eq, refRs1_v15546_eq]
  simp only [refRs1_v15547, source_select]
  all_goals rfl

private def refRs1_v15548 (s : State) (i : Inputs) : Bool := if v14595 s i = 1 then refRs1_v15399 s i else refRs1_v15547 s i
private theorem refRs1_v15548_eq (s : State) (i : Inputs) :
    v15548 s i = if refRs1_v15548 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15548, refRs1_v15399_eq, refRs1_v15547_eq]
  simp only [refRs1_v15548, source_select]
  all_goals rfl

private def refRs1_v15549 (s : State) (i : Inputs) : Bool := if v14589 s i = 1 then refRs1_v15398 s i else refRs1_v15548 s i
private theorem refRs1_v15549_eq (s : State) (i : Inputs) :
    v15549 s i = if refRs1_v15549 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15549, refRs1_v15398_eq, refRs1_v15548_eq]
  simp only [refRs1_v15549, source_select]
  all_goals rfl

private def refRs1_v15550 (s : State) (i : Inputs) : Bool := if v14583 s i = 1 then refRs1_v15397 s i else refRs1_v15549 s i
private theorem refRs1_v15550_eq (s : State) (i : Inputs) :
    v15550 s i = if refRs1_v15550 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15550, refRs1_v15397_eq, refRs1_v15549_eq]
  simp only [refRs1_v15550, source_select]
  all_goals rfl

private def refRs1_v15551 (s : State) (i : Inputs) : Bool := if v14560 s i = 1 then refRs1_v15550 s i else refRs1_v15076 s i
private theorem refRs1_v15551_eq (s : State) (i : Inputs) :
    v15551 s i = if refRs1_v15551 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 := by
  rw [v15551, refRs1_v15550_eq, refRs1_v15076_eq]
  simp only [refRs1_v15551, source_select]
  all_goals rfl

/-- Whether the actual reference decoder selects a register field for rs1. -/
def referenceUsesRs1 (s : State) (i : Inputs) : Bool := refRs1_v15551 s i

theorem reference_rs1_address (s : State) (i : Inputs) :
    v15551 s i = if referenceUsesRs1 s i then BitVec.extractLsb' 15 5 (v14575 s i) else 0 :=
  refRs1_v15551_eq s i

theorem committed_reference_rs1_address (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (used : referenceUsesRs1 (step s i) next = true) :
    v15551 (step s i) next = BitVec.extractLsb' 15 5
      s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr := by
  rw [reference_rs1_address, used]
  simp only [Bool.true_eq, ↓reduceIte, v14575, v14560, v14559, v14558, commit,
    v14573, v14572, v14571, v14570, v14569]
  rw [capture_decode_cf_instr s i next commit]
  simp (config := { maxSteps := 1000000 }) (disch := omega) only [v25333, v11547, source_extract_low]

#print axioms committed_reference_rs1_address

theorem reference_uses_rs1_of_addi_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15071 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]
#print axioms reference_uses_rs1_of_addi_match

theorem reference_uses_rs1_of_lb_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14893 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_lh_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14885 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_lw_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14877 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_ld_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14710 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_lbu_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14869 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_lhu_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14861 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_lwu_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14718 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_sb_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15186 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_sh_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15180 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_sw_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15174 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_sd_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15160 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_jalr_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14901 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_slti_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15063 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_sltiu_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15055 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_xori_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15031 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_ori_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15039 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_andi_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15047 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_slli64_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14825 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_srli64_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14818 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_srai64_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14811 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_addiw_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14833 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_slliw_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14803 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_srliw_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14796 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_sraiw_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14789 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_register_add_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14989 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_register_sub_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14925 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_register_slt_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14981 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_register_sltu_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14973 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_register_xor_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14949 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_register_or_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14957 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_register_and_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14965 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_register_sll_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14781 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_register_srl_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14773 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_register_sra_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14765 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_branch_beq_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15227 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_branch_bne_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15220 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_branch_blt_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15213 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_branch_bge_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15199 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_branch_bltu_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15206 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs1_of_branch_bgeu_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15192 s i = 1) :
    referenceUsesRs1 s i = true := by
  simp only [referenceUsesRs1, refRs1_v15076, refRs1_v15397, refRs1_v15398, refRs1_v15399, refRs1_v15400, refRs1_v15401, refRs1_v15402, refRs1_v15403, refRs1_v15404, refRs1_v15405, refRs1_v15406, refRs1_v15407, refRs1_v15408, refRs1_v15409, refRs1_v15410, refRs1_v15411, refRs1_v15412, refRs1_v15413, refRs1_v15415, refRs1_v15416, refRs1_v15417, refRs1_v15418, refRs1_v15419, refRs1_v15420, refRs1_v15421, refRs1_v15422, refRs1_v15423, refRs1_v15424, refRs1_v15425, refRs1_v15426, refRs1_v15427, refRs1_v15428, refRs1_v15429, refRs1_v15430, refRs1_v15431, refRs1_v15432, refRs1_v15433, refRs1_v15434, refRs1_v15435, refRs1_v15437, refRs1_v15439, refRs1_v15441, refRs1_v15442, refRs1_v15443, refRs1_v15444, refRs1_v15445, refRs1_v15446, refRs1_v15448, refRs1_v15450, refRs1_v15452, refRs1_v15454, refRs1_v15456, refRs1_v15458, refRs1_v15459, refRs1_v15460, refRs1_v15461, refRs1_v15462, refRs1_v15463, refRs1_v15464, refRs1_v15465, refRs1_v15466, refRs1_v15467, refRs1_v15468, refRs1_v15469, refRs1_v15470, refRs1_v15471, refRs1_v15472, refRs1_v15473, refRs1_v15474, refRs1_v15475, refRs1_v15476, refRs1_v15477, refRs1_v15478, refRs1_v15479, refRs1_v15480, refRs1_v15481, refRs1_v15482, refRs1_v15483, refRs1_v15484, refRs1_v15485, refRs1_v15486, refRs1_v15487, refRs1_v15488, refRs1_v15489, refRs1_v15490, refRs1_v15491, refRs1_v15492, refRs1_v15493, refRs1_v15494, refRs1_v15495, refRs1_v15496, refRs1_v15497, refRs1_v15498, refRs1_v15499, refRs1_v15500, refRs1_v15501, refRs1_v15502, refRs1_v15503, refRs1_v15504, refRs1_v15505, refRs1_v15506, refRs1_v15507, refRs1_v15508, refRs1_v15509, refRs1_v15510, refRs1_v15511, refRs1_v15512, refRs1_v15513, refRs1_v15514, refRs1_v15515, refRs1_v15516, refRs1_v15517, refRs1_v15518, refRs1_v15519, refRs1_v15520, refRs1_v15521, refRs1_v15522, refRs1_v15523, refRs1_v15524, refRs1_v15525, refRs1_v15526, refRs1_v15527, refRs1_v15528, refRs1_v15529, refRs1_v15530, refRs1_v15531, refRs1_v15532, refRs1_v15533, refRs1_v15534, refRs1_v15535, refRs1_v15536, refRs1_v15537, refRs1_v15538, refRs1_v15539, refRs1_v15540, refRs1_v15541, refRs1_v15542, refRs1_v15543, refRs1_v15544, refRs1_v15545, refRs1_v15546, refRs1_v15547, refRs1_v15548, refRs1_v15549, refRs1_v15550, refRs1_v15551, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

private def refRs2_v15144 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15144_eq (s : State) (i : Inputs) :
    v15144 s i = if refRs2_v15144 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15144, v15144, v14606, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15145 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15145_eq (s : State) (i : Inputs) :
    v15145 s i = if refRs2_v15145 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15145, v15145, v14614, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15146 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15146_eq (s : State) (i : Inputs) :
    v15146 s i = if refRs2_v15146 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15146, v15146, v14622, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15147 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15147_eq (s : State) (i : Inputs) :
    v15147 s i = if refRs2_v15147 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15147, v15147, v14630, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15148 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15148_eq (s : State) (i : Inputs) :
    v15148 s i = if refRs2_v15148 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15148, v15148, v14638, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15149 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15149_eq (s : State) (i : Inputs) :
    v15149 s i = if refRs2_v15149 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15149, v15149, v14646, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15150 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15150_eq (s : State) (i : Inputs) :
    v15150 s i = if refRs2_v15150 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15150, v15150, v14654, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15151 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15151_eq (s : State) (i : Inputs) :
    v15151 s i = if refRs2_v15151 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15151, v15151, v14662, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15152 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15152_eq (s : State) (i : Inputs) :
    v15152 s i = if refRs2_v15152 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15152, v15152, v14670, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15153 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15153_eq (s : State) (i : Inputs) :
    v15153 s i = if refRs2_v15153 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15153, v15153, v14678, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15154 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15154_eq (s : State) (i : Inputs) :
    v15154 s i = if refRs2_v15154 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15154, v15154, v14686, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15155 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15155_eq (s : State) (i : Inputs) :
    v15155 s i = if refRs2_v15155 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15155, v15155, v14694, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15156 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15156_eq (s : State) (i : Inputs) :
    v15156 s i = if refRs2_v15156 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15156, v15156, v14702, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15162 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15162_eq (s : State) (i : Inputs) :
    v15162 s i = if refRs2_v15162 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15162, v15162, v15161, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15163 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15163_eq (s : State) (i : Inputs) :
    v15163 s i = if refRs2_v15163 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15163, v15163, v14726, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15164 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15164_eq (s : State) (i : Inputs) :
    v15164 s i = if refRs2_v15164 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15164, v15164, v14734, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15165 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15165_eq (s : State) (i : Inputs) :
    v15165 s i = if refRs2_v15165 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15165, v15165, v14742, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15166 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15166_eq (s : State) (i : Inputs) :
    v15166 s i = if refRs2_v15166 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15166, v15166, v14750, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15167 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15167_eq (s : State) (i : Inputs) :
    v15167 s i = if refRs2_v15167 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15167, v15167, v14758, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15168 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15168_eq (s : State) (i : Inputs) :
    v15168 s i = if refRs2_v15168 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15168, v15168, v14766, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15169 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15169_eq (s : State) (i : Inputs) :
    v15169 s i = if refRs2_v15169 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15169, v15169, v14774, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15170 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15170_eq (s : State) (i : Inputs) :
    v15170 s i = if refRs2_v15170 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15170, v15170, v14782, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15176 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15176_eq (s : State) (i : Inputs) :
    v15176 s i = if refRs2_v15176 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15176, v15176, v15175, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15182 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15182_eq (s : State) (i : Inputs) :
    v15182 s i = if refRs2_v15182 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15182, v15182, v15181, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15188 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15188_eq (s : State) (i : Inputs) :
    v15188 s i = if refRs2_v15188 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15188, v15188, v15187, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15195 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15195_eq (s : State) (i : Inputs) :
    v15195 s i = if refRs2_v15195 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15195, v15195, v15194, v15193, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15202 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15202_eq (s : State) (i : Inputs) :
    v15202 s i = if refRs2_v15202 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15202, v15202, v15201, v15200, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15209 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15209_eq (s : State) (i : Inputs) :
    v15209 s i = if refRs2_v15209 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15209, v15209, v15208, v15207, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15216 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15216_eq (s : State) (i : Inputs) :
    v15216 s i = if refRs2_v15216 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15216, v15216, v15215, v15214, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15223 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15223_eq (s : State) (i : Inputs) :
    v15223 s i = if refRs2_v15223 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15223, v15223, v15222, v15221, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15230 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15230_eq (s : State) (i : Inputs) :
    v15230 s i = if refRs2_v15230 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15230, v15230, v15229, v15228, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15231 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15231_eq (s : State) (i : Inputs) :
    v15231 s i = if refRs2_v15231 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15231, v15231, v14918, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15232 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15232_eq (s : State) (i : Inputs) :
    v15232 s i = if refRs2_v15232 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15232, v15232, v14926, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15233 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15233_eq (s : State) (i : Inputs) :
    v15233 s i = if refRs2_v15233 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15233, v15233, v14934, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15234 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15234_eq (s : State) (i : Inputs) :
    v15234 s i = if refRs2_v15234 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15234, v15234, v14942, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15235 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15235_eq (s : State) (i : Inputs) :
    v15235 s i = if refRs2_v15235 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15235, v15235, v14950, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15236 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15236_eq (s : State) (i : Inputs) :
    v15236 s i = if refRs2_v15236 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15236, v15236, v14958, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15237 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15237_eq (s : State) (i : Inputs) :
    v15237 s i = if refRs2_v15237 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15237, v15237, v14966, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15238 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15238_eq (s : State) (i : Inputs) :
    v15238 s i = if refRs2_v15238 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15238, v15238, v14974, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15239 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15239_eq (s : State) (i : Inputs) :
    v15239 s i = if refRs2_v15239 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15239, v15239, v14982, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15240 (s : State) (i : Inputs) : Bool := true
private theorem refRs2_v15240_eq (s : State) (i : Inputs) :
    v15240 s i = if refRs2_v15240 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15240, v15240, v14990, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15076 (s : State) (i : Inputs) : Bool := false
private theorem refRs2_v15076_eq (s : State) (i : Inputs) :
    v15076 s i = if refRs2_v15076 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  simp (disch := omega) only [refRs2_v15076, v15076, source_extract_low, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

private def refRs2_v15241 (s : State) (i : Inputs) : Bool := if v14989 s i = 1 then refRs2_v15240 s i else refRs2_v15076 s i
private theorem refRs2_v15241_eq (s : State) (i : Inputs) :
    v15241 s i = if refRs2_v15241 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15241, refRs2_v15240_eq, refRs2_v15076_eq]
  simp only [refRs2_v15241, source_select]
  all_goals rfl

private def refRs2_v15242 (s : State) (i : Inputs) : Bool := if v14981 s i = 1 then refRs2_v15239 s i else refRs2_v15241 s i
private theorem refRs2_v15242_eq (s : State) (i : Inputs) :
    v15242 s i = if refRs2_v15242 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15242, refRs2_v15239_eq, refRs2_v15241_eq]
  simp only [refRs2_v15242, source_select]
  all_goals rfl

private def refRs2_v15243 (s : State) (i : Inputs) : Bool := if v14973 s i = 1 then refRs2_v15238 s i else refRs2_v15242 s i
private theorem refRs2_v15243_eq (s : State) (i : Inputs) :
    v15243 s i = if refRs2_v15243 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15243, refRs2_v15238_eq, refRs2_v15242_eq]
  simp only [refRs2_v15243, source_select]
  all_goals rfl

private def refRs2_v15244 (s : State) (i : Inputs) : Bool := if v14965 s i = 1 then refRs2_v15237 s i else refRs2_v15243 s i
private theorem refRs2_v15244_eq (s : State) (i : Inputs) :
    v15244 s i = if refRs2_v15244 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15244, refRs2_v15237_eq, refRs2_v15243_eq]
  simp only [refRs2_v15244, source_select]
  all_goals rfl

private def refRs2_v15245 (s : State) (i : Inputs) : Bool := if v14957 s i = 1 then refRs2_v15236 s i else refRs2_v15244 s i
private theorem refRs2_v15245_eq (s : State) (i : Inputs) :
    v15245 s i = if refRs2_v15245 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15245, refRs2_v15236_eq, refRs2_v15244_eq]
  simp only [refRs2_v15245, source_select]
  all_goals rfl

private def refRs2_v15246 (s : State) (i : Inputs) : Bool := if v14949 s i = 1 then refRs2_v15235 s i else refRs2_v15245 s i
private theorem refRs2_v15246_eq (s : State) (i : Inputs) :
    v15246 s i = if refRs2_v15246 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15246, refRs2_v15235_eq, refRs2_v15245_eq]
  simp only [refRs2_v15246, source_select]
  all_goals rfl

private def refRs2_v15247 (s : State) (i : Inputs) : Bool := if v14941 s i = 1 then refRs2_v15234 s i else refRs2_v15246 s i
private theorem refRs2_v15247_eq (s : State) (i : Inputs) :
    v15247 s i = if refRs2_v15247 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15247, refRs2_v15234_eq, refRs2_v15246_eq]
  simp only [refRs2_v15247, source_select]
  all_goals rfl

private def refRs2_v15248 (s : State) (i : Inputs) : Bool := if v14933 s i = 1 then refRs2_v15233 s i else refRs2_v15247 s i
private theorem refRs2_v15248_eq (s : State) (i : Inputs) :
    v15248 s i = if refRs2_v15248 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15248, refRs2_v15233_eq, refRs2_v15247_eq]
  simp only [refRs2_v15248, source_select]
  all_goals rfl

private def refRs2_v15249 (s : State) (i : Inputs) : Bool := if v14925 s i = 1 then refRs2_v15232 s i else refRs2_v15248 s i
private theorem refRs2_v15249_eq (s : State) (i : Inputs) :
    v15249 s i = if refRs2_v15249 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15249, refRs2_v15232_eq, refRs2_v15248_eq]
  simp only [refRs2_v15249, source_select]
  all_goals rfl

private def refRs2_v15250 (s : State) (i : Inputs) : Bool := if v14917 s i = 1 then refRs2_v15231 s i else refRs2_v15249 s i
private theorem refRs2_v15250_eq (s : State) (i : Inputs) :
    v15250 s i = if refRs2_v15250 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15250, refRs2_v15231_eq, refRs2_v15249_eq]
  simp only [refRs2_v15250, source_select]
  all_goals rfl

private def refRs2_v15251 (s : State) (i : Inputs) : Bool := if v15227 s i = 1 then refRs2_v15230 s i else refRs2_v15250 s i
private theorem refRs2_v15251_eq (s : State) (i : Inputs) :
    v15251 s i = if refRs2_v15251 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15251, refRs2_v15230_eq, refRs2_v15250_eq]
  simp only [refRs2_v15251, source_select]
  all_goals rfl

private def refRs2_v15252 (s : State) (i : Inputs) : Bool := if v15220 s i = 1 then refRs2_v15223 s i else refRs2_v15251 s i
private theorem refRs2_v15252_eq (s : State) (i : Inputs) :
    v15252 s i = if refRs2_v15252 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15252, refRs2_v15223_eq, refRs2_v15251_eq]
  simp only [refRs2_v15252, source_select]
  all_goals rfl

private def refRs2_v15253 (s : State) (i : Inputs) : Bool := if v15213 s i = 1 then refRs2_v15216 s i else refRs2_v15252 s i
private theorem refRs2_v15253_eq (s : State) (i : Inputs) :
    v15253 s i = if refRs2_v15253 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15253, refRs2_v15216_eq, refRs2_v15252_eq]
  simp only [refRs2_v15253, source_select]
  all_goals rfl

private def refRs2_v15254 (s : State) (i : Inputs) : Bool := if v15206 s i = 1 then refRs2_v15209 s i else refRs2_v15253 s i
private theorem refRs2_v15254_eq (s : State) (i : Inputs) :
    v15254 s i = if refRs2_v15254 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15254, refRs2_v15209_eq, refRs2_v15253_eq]
  simp only [refRs2_v15254, source_select]
  all_goals rfl

private def refRs2_v15255 (s : State) (i : Inputs) : Bool := if v15199 s i = 1 then refRs2_v15202 s i else refRs2_v15254 s i
private theorem refRs2_v15255_eq (s : State) (i : Inputs) :
    v15255 s i = if refRs2_v15255 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15255, refRs2_v15202_eq, refRs2_v15254_eq]
  simp only [refRs2_v15255, source_select]
  all_goals rfl

private def refRs2_v15256 (s : State) (i : Inputs) : Bool := if v15192 s i = 1 then refRs2_v15195 s i else refRs2_v15255 s i
private theorem refRs2_v15256_eq (s : State) (i : Inputs) :
    v15256 s i = if refRs2_v15256 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15256, refRs2_v15195_eq, refRs2_v15255_eq]
  simp only [refRs2_v15256, source_select]
  all_goals rfl

private def refRs2_v15257 (s : State) (i : Inputs) : Bool := if v15186 s i = 1 then refRs2_v15188 s i else refRs2_v15256 s i
private theorem refRs2_v15257_eq (s : State) (i : Inputs) :
    v15257 s i = if refRs2_v15257 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15257, refRs2_v15188_eq, refRs2_v15256_eq]
  simp only [refRs2_v15257, source_select]
  all_goals rfl

private def refRs2_v15258 (s : State) (i : Inputs) : Bool := if v15180 s i = 1 then refRs2_v15182 s i else refRs2_v15257 s i
private theorem refRs2_v15258_eq (s : State) (i : Inputs) :
    v15258 s i = if refRs2_v15258 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15258, refRs2_v15182_eq, refRs2_v15257_eq]
  simp only [refRs2_v15258, source_select]
  all_goals rfl

private def refRs2_v15259 (s : State) (i : Inputs) : Bool := if v15174 s i = 1 then refRs2_v15176 s i else refRs2_v15258 s i
private theorem refRs2_v15259_eq (s : State) (i : Inputs) :
    v15259 s i = if refRs2_v15259 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15259, refRs2_v15176_eq, refRs2_v15258_eq]
  simp only [refRs2_v15259, source_select]
  all_goals rfl

private def refRs2_v15260 (s : State) (i : Inputs) : Bool := if v14781 s i = 1 then refRs2_v15170 s i else refRs2_v15259 s i
private theorem refRs2_v15260_eq (s : State) (i : Inputs) :
    v15260 s i = if refRs2_v15260 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15260, refRs2_v15170_eq, refRs2_v15259_eq]
  simp only [refRs2_v15260, source_select]
  all_goals rfl

private def refRs2_v15261 (s : State) (i : Inputs) : Bool := if v14773 s i = 1 then refRs2_v15169 s i else refRs2_v15260 s i
private theorem refRs2_v15261_eq (s : State) (i : Inputs) :
    v15261 s i = if refRs2_v15261 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15261, refRs2_v15169_eq, refRs2_v15260_eq]
  simp only [refRs2_v15261, source_select]
  all_goals rfl

private def refRs2_v15262 (s : State) (i : Inputs) : Bool := if v14765 s i = 1 then refRs2_v15168 s i else refRs2_v15261 s i
private theorem refRs2_v15262_eq (s : State) (i : Inputs) :
    v15262 s i = if refRs2_v15262 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15262, refRs2_v15168_eq, refRs2_v15261_eq]
  simp only [refRs2_v15262, source_select]
  all_goals rfl

private def refRs2_v15263 (s : State) (i : Inputs) : Bool := if v14757 s i = 1 then refRs2_v15167 s i else refRs2_v15262 s i
private theorem refRs2_v15263_eq (s : State) (i : Inputs) :
    v15263 s i = if refRs2_v15263 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15263, refRs2_v15167_eq, refRs2_v15262_eq]
  simp only [refRs2_v15263, source_select]
  all_goals rfl

private def refRs2_v15264 (s : State) (i : Inputs) : Bool := if v14749 s i = 1 then refRs2_v15166 s i else refRs2_v15263 s i
private theorem refRs2_v15264_eq (s : State) (i : Inputs) :
    v15264 s i = if refRs2_v15264 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15264, refRs2_v15166_eq, refRs2_v15263_eq]
  simp only [refRs2_v15264, source_select]
  all_goals rfl

private def refRs2_v15265 (s : State) (i : Inputs) : Bool := if v14741 s i = 1 then refRs2_v15165 s i else refRs2_v15264 s i
private theorem refRs2_v15265_eq (s : State) (i : Inputs) :
    v15265 s i = if refRs2_v15265 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15265, refRs2_v15165_eq, refRs2_v15264_eq]
  simp only [refRs2_v15265, source_select]
  all_goals rfl

private def refRs2_v15266 (s : State) (i : Inputs) : Bool := if v14733 s i = 1 then refRs2_v15164 s i else refRs2_v15265 s i
private theorem refRs2_v15266_eq (s : State) (i : Inputs) :
    v15266 s i = if refRs2_v15266 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15266, refRs2_v15164_eq, refRs2_v15265_eq]
  simp only [refRs2_v15266, source_select]
  all_goals rfl

private def refRs2_v15267 (s : State) (i : Inputs) : Bool := if v14725 s i = 1 then refRs2_v15163 s i else refRs2_v15266 s i
private theorem refRs2_v15267_eq (s : State) (i : Inputs) :
    v15267 s i = if refRs2_v15267 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15267, refRs2_v15163_eq, refRs2_v15266_eq]
  simp only [refRs2_v15267, source_select]
  all_goals rfl

private def refRs2_v15268 (s : State) (i : Inputs) : Bool := if v15160 s i = 1 then refRs2_v15162 s i else refRs2_v15267 s i
private theorem refRs2_v15268_eq (s : State) (i : Inputs) :
    v15268 s i = if refRs2_v15268 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15268, refRs2_v15162_eq, refRs2_v15267_eq]
  simp only [refRs2_v15268, source_select]
  all_goals rfl

private def refRs2_v15269 (s : State) (i : Inputs) : Bool := if v14701 s i = 1 then refRs2_v15156 s i else refRs2_v15268 s i
private theorem refRs2_v15269_eq (s : State) (i : Inputs) :
    v15269 s i = if refRs2_v15269 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15269, refRs2_v15156_eq, refRs2_v15268_eq]
  simp only [refRs2_v15269, source_select]
  all_goals rfl

private def refRs2_v15270 (s : State) (i : Inputs) : Bool := if v14693 s i = 1 then refRs2_v15155 s i else refRs2_v15269 s i
private theorem refRs2_v15270_eq (s : State) (i : Inputs) :
    v15270 s i = if refRs2_v15270 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15270, refRs2_v15155_eq, refRs2_v15269_eq]
  simp only [refRs2_v15270, source_select]
  all_goals rfl

private def refRs2_v15271 (s : State) (i : Inputs) : Bool := if v14685 s i = 1 then refRs2_v15154 s i else refRs2_v15270 s i
private theorem refRs2_v15271_eq (s : State) (i : Inputs) :
    v15271 s i = if refRs2_v15271 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15271, refRs2_v15154_eq, refRs2_v15270_eq]
  simp only [refRs2_v15271, source_select]
  all_goals rfl

private def refRs2_v15272 (s : State) (i : Inputs) : Bool := if v14677 s i = 1 then refRs2_v15153 s i else refRs2_v15271 s i
private theorem refRs2_v15272_eq (s : State) (i : Inputs) :
    v15272 s i = if refRs2_v15272 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15272, refRs2_v15153_eq, refRs2_v15271_eq]
  simp only [refRs2_v15272, source_select]
  all_goals rfl

private def refRs2_v15273 (s : State) (i : Inputs) : Bool := if v14669 s i = 1 then refRs2_v15152 s i else refRs2_v15272 s i
private theorem refRs2_v15273_eq (s : State) (i : Inputs) :
    v15273 s i = if refRs2_v15273 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15273, refRs2_v15152_eq, refRs2_v15272_eq]
  simp only [refRs2_v15273, source_select]
  all_goals rfl

private def refRs2_v15274 (s : State) (i : Inputs) : Bool := if v14661 s i = 1 then refRs2_v15151 s i else refRs2_v15273 s i
private theorem refRs2_v15274_eq (s : State) (i : Inputs) :
    v15274 s i = if refRs2_v15274 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15274, refRs2_v15151_eq, refRs2_v15273_eq]
  simp only [refRs2_v15274, source_select]
  all_goals rfl

private def refRs2_v15275 (s : State) (i : Inputs) : Bool := if v14653 s i = 1 then refRs2_v15150 s i else refRs2_v15274 s i
private theorem refRs2_v15275_eq (s : State) (i : Inputs) :
    v15275 s i = if refRs2_v15275 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15275, refRs2_v15150_eq, refRs2_v15274_eq]
  simp only [refRs2_v15275, source_select]
  all_goals rfl

private def refRs2_v15276 (s : State) (i : Inputs) : Bool := if v14645 s i = 1 then refRs2_v15149 s i else refRs2_v15275 s i
private theorem refRs2_v15276_eq (s : State) (i : Inputs) :
    v15276 s i = if refRs2_v15276 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15276, refRs2_v15149_eq, refRs2_v15275_eq]
  simp only [refRs2_v15276, source_select]
  all_goals rfl

private def refRs2_v15277 (s : State) (i : Inputs) : Bool := if v14637 s i = 1 then refRs2_v15148 s i else refRs2_v15276 s i
private theorem refRs2_v15277_eq (s : State) (i : Inputs) :
    v15277 s i = if refRs2_v15277 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15277, refRs2_v15148_eq, refRs2_v15276_eq]
  simp only [refRs2_v15277, source_select]
  all_goals rfl

private def refRs2_v15278 (s : State) (i : Inputs) : Bool := if v14629 s i = 1 then refRs2_v15147 s i else refRs2_v15277 s i
private theorem refRs2_v15278_eq (s : State) (i : Inputs) :
    v15278 s i = if refRs2_v15278 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15278, refRs2_v15147_eq, refRs2_v15277_eq]
  simp only [refRs2_v15278, source_select]
  all_goals rfl

private def refRs2_v15279 (s : State) (i : Inputs) : Bool := if v14621 s i = 1 then refRs2_v15146 s i else refRs2_v15278 s i
private theorem refRs2_v15279_eq (s : State) (i : Inputs) :
    v15279 s i = if refRs2_v15279 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15279, refRs2_v15146_eq, refRs2_v15278_eq]
  simp only [refRs2_v15279, source_select]
  all_goals rfl

private def refRs2_v15280 (s : State) (i : Inputs) : Bool := if v14613 s i = 1 then refRs2_v15145 s i else refRs2_v15279 s i
private theorem refRs2_v15280_eq (s : State) (i : Inputs) :
    v15280 s i = if refRs2_v15280 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15280, refRs2_v15145_eq, refRs2_v15279_eq]
  simp only [refRs2_v15280, source_select]
  all_goals rfl

private def refRs2_v15281 (s : State) (i : Inputs) : Bool := if v14578 s i = 1 then refRs2_v15144 s i else refRs2_v15280 s i
private theorem refRs2_v15281_eq (s : State) (i : Inputs) :
    v15281 s i = if refRs2_v15281 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15281, refRs2_v15144_eq, refRs2_v15280_eq]
  simp only [refRs2_v15281, source_select]
  all_goals rfl

private def refRs2_v15282 (s : State) (i : Inputs) : Bool := if v14560 s i = 1 then refRs2_v15281 s i else refRs2_v15076 s i
private theorem refRs2_v15282_eq (s : State) (i : Inputs) :
    v15282 s i = if refRs2_v15282 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 := by
  rw [v15282, refRs2_v15281_eq, refRs2_v15076_eq]
  simp only [refRs2_v15282, source_select]
  all_goals rfl

/-- Whether the actual reference decoder selects a register field for rs2. -/
def referenceUsesRs2 (s : State) (i : Inputs) : Bool := refRs2_v15282 s i

theorem reference_rs2_address (s : State) (i : Inputs) :
    v15282 s i = if referenceUsesRs2 s i then BitVec.extractLsb' 20 5 (v14575 s i) else 0 :=
  refRs2_v15282_eq s i

theorem committed_reference_rs2_address (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (used : referenceUsesRs2 (step s i) next = true) :
    v15282 (step s i) next = BitVec.extractLsb' 20 5
      s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr := by
  rw [reference_rs2_address, used]
  simp only [Bool.true_eq, ↓reduceIte, v14575, v14560, v14559, v14558, commit,
    v14573, v14572, v14571, v14570, v14569]
  rw [capture_decode_cf_instr s i next commit]
  simp (config := { maxSteps := 1000000 }) (disch := omega) only [v25333, v11547, source_extract_low]

#print axioms committed_reference_rs2_address

theorem reference_uses_rs2_of_register_add_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14989 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_register_sub_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14925 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_register_slt_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14981 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_register_sltu_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14973 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_register_xor_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14949 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_register_or_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14957 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_register_and_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14965 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_register_sll_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14781 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_register_srl_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14773 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_register_sra_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v14765 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_store_sb_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15186 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_store_sh_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15180 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_store_sw_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15174 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_store_sd_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15160 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_branch_beq_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15227 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_branch_bne_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15220 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_branch_blt_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15213 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_branch_bge_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15199 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_branch_bltu_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15206 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]

theorem reference_uses_rs2_of_branch_bgeu_match (s : State) (i : Inputs)
    (commit : v9 s i = 1) (matched : v15192 s i = 1) :
    referenceUsesRs2 s i = true := by
  simp only [referenceUsesRs2, refRs2_v15076, refRs2_v15144, refRs2_v15145, refRs2_v15146, refRs2_v15147, refRs2_v15148, refRs2_v15149, refRs2_v15150, refRs2_v15151, refRs2_v15152, refRs2_v15153, refRs2_v15154, refRs2_v15155, refRs2_v15156, refRs2_v15162, refRs2_v15163, refRs2_v15164, refRs2_v15165, refRs2_v15166, refRs2_v15167, refRs2_v15168, refRs2_v15169, refRs2_v15170, refRs2_v15176, refRs2_v15182, refRs2_v15188, refRs2_v15195, refRs2_v15202, refRs2_v15209, refRs2_v15216, refRs2_v15223, refRs2_v15230, refRs2_v15231, refRs2_v15232, refRs2_v15233, refRs2_v15234, refRs2_v15235, refRs2_v15236, refRs2_v15237, refRs2_v15238, refRs2_v15239, refRs2_v15240, refRs2_v15241, refRs2_v15242, refRs2_v15243, refRs2_v15244, refRs2_v15245, refRs2_v15246, refRs2_v15247, refRs2_v15248, refRs2_v15249, refRs2_v15250, refRs2_v15251, refRs2_v15252, refRs2_v15253, refRs2_v15254, refRs2_v15255, refRs2_v15256, refRs2_v15257, refRs2_v15258, refRs2_v15259, refRs2_v15260, refRs2_v15261, refRs2_v15262, refRs2_v15263, refRs2_v15264, refRs2_v15265, refRs2_v15266, refRs2_v15267, refRs2_v15268, refRs2_v15269, refRs2_v15270, refRs2_v15271, refRs2_v15272, refRs2_v15273, refRs2_v15274, refRs2_v15275, refRs2_v15276, refRs2_v15277, refRs2_v15278, refRs2_v15279, refRs2_v15280, refRs2_v15281, refRs2_v15282, v14560, v14559, v14558, commit, matched, ↓reduceIte, ite_self]
end NutShellProofs
