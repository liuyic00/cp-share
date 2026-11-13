import Proofs.BoothRowPacking
import Proofs.BoothCorrectionDistribution

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace HierarchicalBooth

def firstPacked (raw : BitVec 66) : BitVec 130 :=
  (~~~(raw.extractLsb' 65 1) ++ raw.extractLsb' 65 1 ++ raw.extractLsb' 65 1 ++ raw).setWidth 130

def nextPacked (last : Bool) (raw : BitVec 66) (previous : BitVec 2) : BitVec 130 :=
  if last then (~~~(raw.extractLsb' 65 1) ++ raw ++ previous).setWidth 130
  else (1#1 ++ ~~~(raw.extractLsb' 65 1) ++ raw ++ previous).setWidth 130

def rowBias (k : Nat) : BitVec 130 :=
  if k = 31 then BitVec.ofNat 130 (2^68) else BitVec.ofNat 130 (3 * 2^68)

private theorem bias_cancels : BitVec.ofNat 130 (2^68) + weightedBits 32 rowBias = 0 := by
  decide

private theorem regroup_values (a b c d e : BitVec 130) :
    (a + b) + (c + d) + e = (a + c + e) + (b + d) := by ac_rfl

private theorem shift_two (x : BitVec 130) : x <<< 2 = 4 * x := by bv_decide

/-- Packed rows include the previous row's correction and constant sign biases.
    The biases cancel modulo the 130-bit output width. -/
theorem packed_sum (raw : Nat → BitVec 66) (correction : Nat → BitVec 2) :
    firstPacked (raw 0) +
      weightedBits 32 (fun k => nextPacked (decide (k = 31)) (raw (k + 1)) (correction k)) +
      BitVec.ofNat 130 (4^32) * (correction 32).setWidth 130 =
    weightedBits 33 (fun k => (raw k).signExtend 130 + (correction k).setWidth 130) := by
  have rows : (fun k => nextPacked (decide (k = 31)) (raw (k + 1)) (correction k)) =
      (fun k => (4 * (raw (k + 1)).signExtend 130 + (correction k).setWidth 130) + rowBias k) := by
    funext k
    by_cases last : k = 31
    · simp only [nextPacked, rowBias, last, decide_true, if_true]
      rw [last_row, shift_two]
    · simp only [nextPacked, rowBias, last, decide_false, Bool.false_eq_true, if_false]
      rw [middle_row, shift_two]
  rw [firstPacked, first_row, rows, weightedBits_add]
  rw [regroup_values, bias_cancels]
  simp only [show (0 : BitVec 130) = 0#130 from rfl, BitVec.add_zero]
  exact distribute_corrections 32 (fun k => (raw k).signExtend 130) (fun k => (correction k).setWidth 130)

end HierarchicalBooth
