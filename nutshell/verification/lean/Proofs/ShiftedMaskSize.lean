import Proofs.MemoryMaskSize
import Proofs.MemoryMaskCapture
import Proofs.MemoryAlignmentCorrespondence
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096

def MemoryOp.sizeBits (op : MemoryOp) : BitVec 7 :=
  BitVec.ofNat 7 (8 * 2 ^ op.alignmentBits)

theorem mask_offset_1_1 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 1) :
    BitVec.extractLsb' 0 1 a = 1 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_1_3 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 3) :
    BitVec.extractLsb' 0 1 a = 1 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_1_5 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 5) :
    BitVec.extractLsb' 0 1 a = 1 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_1_7 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 7) :
    BitVec.extractLsb' 0 1 a = 1 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_2_1 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 1) :
    BitVec.extractLsb' 0 2 a = 1 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_2_2 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 2) :
    BitVec.extractLsb' 0 2 a = 2 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_2_3 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 3) :
    BitVec.extractLsb' 0 2 a = 3 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_2_5 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 5) :
    BitVec.extractLsb' 0 2 a = 1 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_2_6 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 6) :
    BitVec.extractLsb' 0 2 a = 2 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_2_7 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 7) :
    BitVec.extractLsb' 0 2 a = 3 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_3_1 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 1) :
    BitVec.extractLsb' 0 3 a = 1 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_3_2 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 2) :
    BitVec.extractLsb' 0 3 a = 2 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_3_3 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 3) :
    BitVec.extractLsb' 0 3 a = 3 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_3_4 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 4) :
    BitVec.extractLsb' 0 3 a = 4 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_3_5 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 5) :
    BitVec.extractLsb' 0 3 a = 5 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_3_6 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 6) :
    BitVec.extractLsb' 0 3 a = 6 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem mask_offset_3_7 (a : BitVec 64) (h : BitVec.extractLsb' 0 3 a = 7) :
    BitVec.extractLsb' 0 3 a = 7 := by
  have low := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp at low ⊢
  omega
theorem shifted_load_mask_size (s check : State) (i ci : Inputs) (operation : MemoryOp)
    (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (aligned : v11628 s i = 1)
    (mask : v30865 check ci = v14480 s i) :
    v31183 check ci = operation.sizeBits := by
  have alignment := normal_memory_alignment s i operation op outer
  have base := memory_mask_before_shift s i operation op outer
  have bound := (BitVec.extractLsb' 0 3 (v11612 s i)).isLt
  have offsets : (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 0 ∨ (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 1 ∨ (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 2 ∨ (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 3 ∨ (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 4 ∨ (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 5 ∨ (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 6 ∨ (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 7 := by omega
  cases operation with
  | lb =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_1
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_2
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_4
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_8
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_16
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_32
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_64
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_128
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
  | lh =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_3
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_12
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_48
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_192
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
  | lw =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_15
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_2 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_240
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_6 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
  | ld =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_255
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_2 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_4 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_6 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
  | lbu =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_1
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_2
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_4
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_8
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_16
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_32
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_64
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_128
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
  | lhu =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_3
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_12
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_48
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_192
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
  | lwu =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_15
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_2 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_240
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_6 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
  | sb =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_1
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_2
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_4
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_8
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_16
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_32
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_64
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_128
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
  | sh =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_3
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_12
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_48
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_192
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
  | sw =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_15
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_2 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_240
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_6 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
  | sd =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply load_checker_size_mask_255
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_2 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_4 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_6 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
#print axioms shifted_load_mask_size
theorem shifted_store_mask_size (s check : State) (i ci : Inputs) (operation : MemoryOp)
    (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (aligned : v11628 s i = 1)
    (mask : v30869 check ci = v14480 s i) :
    v31337 check ci = operation.sizeBits := by
  have alignment := normal_memory_alignment s i operation op outer
  have base := memory_mask_before_shift s i operation op outer
  have bound := (BitVec.extractLsb' 0 3 (v11612 s i)).isLt
  have offsets : (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 0 ∨ (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 1 ∨ (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 2 ∨ (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 3 ∨ (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 4 ∨ (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 5 ∨ (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 6 ∨ (BitVec.extractLsb' 0 3 (v11612 s i)).toNat = 7 := by omega
  cases operation with
  | lb =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_1
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_2
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_4
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_8
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_16
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_32
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_64
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_128
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
  | lh =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_3
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_12
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_48
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_192
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
  | lw =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_15
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_2 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_240
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_6 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
  | ld =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_255
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_2 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_4 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_6 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
  | lbu =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_1
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_2
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_4
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_8
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_16
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_32
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_64
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_128
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
  | lhu =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_3
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_12
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_48
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_192
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
  | lwu =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_15
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_2 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_240
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_6 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
  | sb =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_1
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_2
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_4
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_8
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_16
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_32
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_64
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_128
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
  | sh =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_3
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_12
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_48
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_192
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_1_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
  | sw =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_15
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_2 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_240
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_6 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_2_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
  | sd =>
    rcases offsets with h | h | h | h | h | h | h | h
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      apply store_checker_size_mask_255
      rw [mask]
      simp [v14480, v14479, v14478, v14477, v14476, v14475, v14474,
        v14473, v14452, v10038, base, MemoryOp.byteMask, offset]
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_1 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_2 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_3 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_4 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_5 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_6 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
    · have offset : BitVec.extractLsb' 0 3 (v11612 s i) = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
      have low := mask_offset_3_7 _ offset
      simp [MemoryOp.alignmentBits, low, aligned] at alignment
#print axioms shifted_store_mask_size
end NutShellProofs
