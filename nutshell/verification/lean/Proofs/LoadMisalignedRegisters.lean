import Proofs.LoadAlignmentFlags
import Proofs.LoadMisalignedWrite
namespace NutShellProofs
open nNutCore
theorem reference_misaligned_load_hold_1 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1440_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = s.g45.r1440_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_1 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_1 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_1 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_1 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_1 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_2 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1441_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = s.g45.r1441_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_2 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_2 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_2 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_2 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_2 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_3 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1442_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = s.g45.r1442_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_3 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_3 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_3 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_3 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_3 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_4 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1443_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = s.g45.r1443_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_4 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_4 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_4 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_4 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_4 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_5 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1444_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = s.g45.r1444_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_5 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_5 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_5 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_5 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_5 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_6 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1445_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = s.g45.r1445_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_6 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_6 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_6 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_6 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_6 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_7 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1446_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = s.g45.r1446_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_7 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_7 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_7 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_7 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_7 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_8 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1447_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = s.g45.r1447_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_8 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_8 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_8 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_8 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_8 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_9 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1448_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = s.g45.r1448_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_9 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_9 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_9 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_9 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_9 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_10 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1449_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = s.g45.r1449_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_10 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_10 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_10 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_10 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_10 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_11 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1450_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = s.g45.r1450_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_11 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_11 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_11 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_11 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_11 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_12 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1451_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = s.g45.r1451_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_12 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_12 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_12 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_12 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_12 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_13 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1452_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = s.g45.r1452_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_13 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_13 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_13 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_13 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_13 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_14 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1453_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = s.g45.r1453_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_14 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_14 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_14 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_14 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_14 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_15 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1454_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = s.g45.r1454_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_15 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_15 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_15 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_15 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_15 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_16 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1455_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = s.g45.r1455_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_16 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_16 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_16 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_16 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_16 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_17 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1456_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = s.g45.r1456_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_17 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_17 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_17 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_17 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_17 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_18 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1457_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = s.g45.r1457_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_18 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_18 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_18 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_18 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_18 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_19 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1458_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = s.g45.r1458_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_19 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_19 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_19 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_19 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_19 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_20 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1459_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = s.g45.r1459_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_20 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_20 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_20 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_20 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_20 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_21 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1460_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = s.g45.r1460_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_21 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_21 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_21 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_21 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_21 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_22 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1461_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = s.g45.r1461_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_22 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_22 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_22 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_22 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_22 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_23 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1462_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = s.g45.r1462_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_23 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_23 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_23 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_23 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_23 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_24 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1463_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = s.g45.r1463_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_24 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_24 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_24 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_24 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_24 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_25 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1464_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = s.g45.r1464_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_25 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_25 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_25 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_25 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_25 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_26 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1465_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = s.g45.r1465_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_26 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_26 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_26 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_26 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_26 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_27 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1466_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = s.g45.r1466_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_27 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_27 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_27 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_27 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_27 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_28 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1467_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = s.g45.r1467_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_28 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_28 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_28 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_28 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_28 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_29 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1468_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = s.g45.r1468_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_29 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_29 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_29 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_29 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_29 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_30 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1469_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = s.g45.r1469_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_30 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_30 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_30 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_30 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_30 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem reference_misaligned_load_hold_31 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i) :
    (step s i).g45.r1470_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = s.g45.r1470_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb | lbu => exact False.elim (misaligned trivial)
  | lh =>
    have eq := reference_load_lh_register_31 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lw =>
    have eq := reference_load_lw_register_31 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | ld =>
    have eq := reference_load_ld_register_31 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lhu =>
    have eq := reference_load_lhu_register_31 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
  | lwu =>
    have eq := reference_load_lwu_register_31 s i reset commit matched
    simp only [referenceLoadAligned] at misaligned
    simpa only [misaligned, false_and, ↓reduceIte] using eq
theorem misaligned_load_registers_aligned_step (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (misaligned : ¬ referenceLoadAligned operation s i)
    (aligned : ArchitecturalRegistersAligned s) (disabled : v11462 s i = 0) :
    ArchitecturalRegistersAligned (step s i) := by
  rcases aligned with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [reference_misaligned_load_hold_1 s i operation load reset commit matched misaligned,
      dut_register_disabled_1 s i reset disabled]
    exact h1
  · rw [reference_misaligned_load_hold_2 s i operation load reset commit matched misaligned,
      dut_register_disabled_2 s i reset disabled]
    exact h2
  · rw [reference_misaligned_load_hold_3 s i operation load reset commit matched misaligned,
      dut_register_disabled_3 s i reset disabled]
    exact h3
  · rw [reference_misaligned_load_hold_4 s i operation load reset commit matched misaligned,
      dut_register_disabled_4 s i reset disabled]
    exact h4
  · rw [reference_misaligned_load_hold_5 s i operation load reset commit matched misaligned,
      dut_register_disabled_5 s i reset disabled]
    exact h5
  · rw [reference_misaligned_load_hold_6 s i operation load reset commit matched misaligned,
      dut_register_disabled_6 s i reset disabled]
    exact h6
  · rw [reference_misaligned_load_hold_7 s i operation load reset commit matched misaligned,
      dut_register_disabled_7 s i reset disabled]
    exact h7
  · rw [reference_misaligned_load_hold_8 s i operation load reset commit matched misaligned,
      dut_register_disabled_8 s i reset disabled]
    exact h8
  · rw [reference_misaligned_load_hold_9 s i operation load reset commit matched misaligned,
      dut_register_disabled_9 s i reset disabled]
    exact h9
  · rw [reference_misaligned_load_hold_10 s i operation load reset commit matched misaligned,
      dut_register_disabled_10 s i reset disabled]
    exact h10
  · rw [reference_misaligned_load_hold_11 s i operation load reset commit matched misaligned,
      dut_register_disabled_11 s i reset disabled]
    exact h11
  · rw [reference_misaligned_load_hold_12 s i operation load reset commit matched misaligned,
      dut_register_disabled_12 s i reset disabled]
    exact h12
  · rw [reference_misaligned_load_hold_13 s i operation load reset commit matched misaligned,
      dut_register_disabled_13 s i reset disabled]
    exact h13
  · rw [reference_misaligned_load_hold_14 s i operation load reset commit matched misaligned,
      dut_register_disabled_14 s i reset disabled]
    exact h14
  · rw [reference_misaligned_load_hold_15 s i operation load reset commit matched misaligned,
      dut_register_disabled_15 s i reset disabled]
    exact h15
  · rw [reference_misaligned_load_hold_16 s i operation load reset commit matched misaligned,
      dut_register_disabled_16 s i reset disabled]
    exact h16
  · rw [reference_misaligned_load_hold_17 s i operation load reset commit matched misaligned,
      dut_register_disabled_17 s i reset disabled]
    exact h17
  · rw [reference_misaligned_load_hold_18 s i operation load reset commit matched misaligned,
      dut_register_disabled_18 s i reset disabled]
    exact h18
  · rw [reference_misaligned_load_hold_19 s i operation load reset commit matched misaligned,
      dut_register_disabled_19 s i reset disabled]
    exact h19
  · rw [reference_misaligned_load_hold_20 s i operation load reset commit matched misaligned,
      dut_register_disabled_20 s i reset disabled]
    exact h20
  · rw [reference_misaligned_load_hold_21 s i operation load reset commit matched misaligned,
      dut_register_disabled_21 s i reset disabled]
    exact h21
  · rw [reference_misaligned_load_hold_22 s i operation load reset commit matched misaligned,
      dut_register_disabled_22 s i reset disabled]
    exact h22
  · rw [reference_misaligned_load_hold_23 s i operation load reset commit matched misaligned,
      dut_register_disabled_23 s i reset disabled]
    exact h23
  · rw [reference_misaligned_load_hold_24 s i operation load reset commit matched misaligned,
      dut_register_disabled_24 s i reset disabled]
    exact h24
  · rw [reference_misaligned_load_hold_25 s i operation load reset commit matched misaligned,
      dut_register_disabled_25 s i reset disabled]
    exact h25
  · rw [reference_misaligned_load_hold_26 s i operation load reset commit matched misaligned,
      dut_register_disabled_26 s i reset disabled]
    exact h26
  · rw [reference_misaligned_load_hold_27 s i operation load reset commit matched misaligned,
      dut_register_disabled_27 s i reset disabled]
    exact h27
  · rw [reference_misaligned_load_hold_28 s i operation load reset commit matched misaligned,
      dut_register_disabled_28 s i reset disabled]
    exact h28
  · rw [reference_misaligned_load_hold_29 s i operation load reset commit matched misaligned,
      dut_register_disabled_29 s i reset disabled]
    exact h29
  · rw [reference_misaligned_load_hold_30 s i operation load reset commit matched misaligned,
      dut_register_disabled_30 s i reset disabled]
    exact h30
  · rw [reference_misaligned_load_hold_31 s i operation load reset commit matched misaligned,
      dut_register_disabled_31 s i reset disabled]
    exact h31
#print axioms misaligned_load_registers_aligned_step
end NutShellProofs
