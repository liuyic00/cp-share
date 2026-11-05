import Proofs.ReferenceLoadRegisters
import Proofs.LoadWriteEnable
import Proofs.LoadResultFormat
namespace NutShellProofs
open nNutCore
def referenceLoadResult (operation : MemoryOp) (s : State) (i : Inputs) : BitVec 64 :=
  match operation with
  | .lb => v16428 s i
  | .lh => v16413 s i
  | .lw => v16392 s i
  | .ld => v16189 s i
  | .lbu => v16370 s i
  | .lhu => v16356 s i
  | .lwu => v16210 s i
  | _ => 0
def referenceLoadAligned (operation : MemoryOp) (s : State) (i : Inputs) : Prop :=
  match operation with
  | .lb => True
  | .lh => v16398 s i = 1
  | .lw => v16377 s i = 1
  | .ld => v16170 s i = 1
  | .lbu => True
  | .lhu => v16342 s i = 1
  | .lwu => v16196 s i = 1
  | _ => False
theorem reference_load_register_1 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1440_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 =
      if v15142 s i = 1 then referenceLoadResult operation s i else s.g45.r1440_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_1 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_1 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_1 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_1 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_1 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_1 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_1 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_1
theorem reference_load_register_2 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1441_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 =
      if v15142 s i = 2 then referenceLoadResult operation s i else s.g45.r1441_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_2 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_2 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_2 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_2 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_2 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_2 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_2 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_2
theorem reference_load_register_3 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1442_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 =
      if v15142 s i = 3 then referenceLoadResult operation s i else s.g45.r1442_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_3 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_3 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_3 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_3 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_3 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_3 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_3 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_3
theorem reference_load_register_4 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1443_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 =
      if v15142 s i = 4 then referenceLoadResult operation s i else s.g45.r1443_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_4 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_4 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_4 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_4 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_4 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_4 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_4 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_4
theorem reference_load_register_5 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1444_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 =
      if v15142 s i = 5 then referenceLoadResult operation s i else s.g45.r1444_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_5 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_5 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_5 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_5 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_5 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_5 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_5 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_5
theorem reference_load_register_6 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1445_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 =
      if v15142 s i = 6 then referenceLoadResult operation s i else s.g45.r1445_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_6 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_6 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_6 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_6 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_6 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_6 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_6 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_6
theorem reference_load_register_7 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1446_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 =
      if v15142 s i = 7 then referenceLoadResult operation s i else s.g45.r1446_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_7 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_7 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_7 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_7 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_7 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_7 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_7 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_7
theorem reference_load_register_8 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1447_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 =
      if v15142 s i = 8 then referenceLoadResult operation s i else s.g45.r1447_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_8 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_8 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_8 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_8 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_8 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_8 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_8 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_8
theorem reference_load_register_9 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1448_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 =
      if v15142 s i = 9 then referenceLoadResult operation s i else s.g45.r1448_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_9 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_9 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_9 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_9 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_9 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_9 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_9 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_9
theorem reference_load_register_10 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1449_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 =
      if v15142 s i = 10 then referenceLoadResult operation s i else s.g45.r1449_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_10 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_10 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_10 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_10 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_10 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_10 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_10 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_10
theorem reference_load_register_11 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1450_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 =
      if v15142 s i = 11 then referenceLoadResult operation s i else s.g45.r1450_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_11 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_11 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_11 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_11 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_11 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_11 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_11 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_11
theorem reference_load_register_12 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1451_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 =
      if v15142 s i = 12 then referenceLoadResult operation s i else s.g45.r1451_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_12 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_12 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_12 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_12 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_12 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_12 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_12 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_12
theorem reference_load_register_13 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1452_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 =
      if v15142 s i = 13 then referenceLoadResult operation s i else s.g45.r1452_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_13 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_13 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_13 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_13 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_13 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_13 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_13 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_13
theorem reference_load_register_14 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1453_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 =
      if v15142 s i = 14 then referenceLoadResult operation s i else s.g45.r1453_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_14 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_14 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_14 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_14 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_14 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_14 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_14 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_14
theorem reference_load_register_15 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1454_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 =
      if v15142 s i = 15 then referenceLoadResult operation s i else s.g45.r1454_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_15 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_15 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_15 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_15 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_15 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_15 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_15 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_15
theorem reference_load_register_16 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1455_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 =
      if v15142 s i = 16 then referenceLoadResult operation s i else s.g45.r1455_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_16 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_16 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_16 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_16 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_16 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_16 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_16 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_16
theorem reference_load_register_17 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1456_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 =
      if v15142 s i = 17 then referenceLoadResult operation s i else s.g45.r1456_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_17 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_17 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_17 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_17 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_17 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_17 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_17 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_17
theorem reference_load_register_18 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1457_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 =
      if v15142 s i = 18 then referenceLoadResult operation s i else s.g45.r1457_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_18 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_18 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_18 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_18 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_18 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_18 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_18 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_18
theorem reference_load_register_19 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1458_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 =
      if v15142 s i = 19 then referenceLoadResult operation s i else s.g45.r1458_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_19 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_19 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_19 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_19 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_19 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_19 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_19 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_19
theorem reference_load_register_20 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1459_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 =
      if v15142 s i = 20 then referenceLoadResult operation s i else s.g45.r1459_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_20 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_20 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_20 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_20 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_20 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_20 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_20 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_20
theorem reference_load_register_21 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1460_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 =
      if v15142 s i = 21 then referenceLoadResult operation s i else s.g45.r1460_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_21 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_21 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_21 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_21 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_21 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_21 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_21 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_21
theorem reference_load_register_22 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1461_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 =
      if v15142 s i = 22 then referenceLoadResult operation s i else s.g45.r1461_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_22 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_22 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_22 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_22 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_22 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_22 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_22 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_22
theorem reference_load_register_23 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1462_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 =
      if v15142 s i = 23 then referenceLoadResult operation s i else s.g45.r1462_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_23 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_23 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_23 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_23 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_23 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_23 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_23 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_23
theorem reference_load_register_24 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1463_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 =
      if v15142 s i = 24 then referenceLoadResult operation s i else s.g45.r1463_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_24 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_24 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_24 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_24 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_24 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_24 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_24 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_24
theorem reference_load_register_25 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1464_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 =
      if v15142 s i = 25 then referenceLoadResult operation s i else s.g45.r1464_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_25 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_25 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_25 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_25 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_25 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_25 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_25 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_25
theorem reference_load_register_26 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1465_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 =
      if v15142 s i = 26 then referenceLoadResult operation s i else s.g45.r1465_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_26 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_26 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_26 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_26 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_26 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_26 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_26 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_26
theorem reference_load_register_27 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1466_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 =
      if v15142 s i = 27 then referenceLoadResult operation s i else s.g45.r1466_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_27 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_27 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_27 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_27 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_27 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_27 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_27 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_27
theorem reference_load_register_28 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1467_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 =
      if v15142 s i = 28 then referenceLoadResult operation s i else s.g45.r1467_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_28 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_28 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_28 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_28 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_28 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_28 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_28 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_28
theorem reference_load_register_29 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1468_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 =
      if v15142 s i = 29 then referenceLoadResult operation s i else s.g45.r1468_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_29 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_29 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_29 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_29 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_29 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_29 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_29 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_29
theorem reference_load_register_30 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1469_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 =
      if v15142 s i = 30 then referenceLoadResult operation s i else s.g45.r1469_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_30 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_30 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_30 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_30 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_30 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_30 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_30 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_30
theorem reference_load_register_31 (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (aligned : referenceLoadAligned operation s i) :
    (step s i).g45.r1470_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 =
      if v15142 s i = 31 then referenceLoadResult operation s i else s.g45.r1470_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 := by
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb =>
    have eq := reference_load_lb_register_31 s i reset commit matched
    exact eq
  | lh =>
    have eq := reference_load_lh_register_31 s i reset commit matched
    have gate : v16398 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lw =>
    have eq := reference_load_lw_register_31 s i reset commit matched
    have gate : v16377 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | ld =>
    have eq := reference_load_ld_register_31 s i reset commit matched
    have gate : v16170 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lbu =>
    have eq := reference_load_lbu_register_31 s i reset commit matched
    exact eq
  | lhu =>
    have eq := reference_load_lhu_register_31 s i reset commit matched
    have gate : v16342 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
  | lwu =>
    have eq := reference_load_lwu_register_31 s i reset commit matched
    have gate : v16196 s i = 1 := aligned
    simpa only [referenceLoadResult, gate, true_and] using eq
#print axioms reference_load_register_31
theorem load_registers_aligned_step (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (immediate : v14575 s i &&& (28799 : BitVec 32) = operation.encoding.setWidth 32)
    (targetAligned : referenceLoadAligned operation s i)
    (aligned : ArchitecturalRegistersAligned s)
    (destination : v11465 s i = v15142 s i)
    (write : v11462 s i = 1) (result : v11842 s i = referenceLoadResult operation s i) :
    ArchitecturalRegistersAligned (step s i) := by

  rcases aligned with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [reference_load_register_1 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 1
    · rw [dut_register_write_1 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_1 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h1
  · rw [reference_load_register_2 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 2
    · rw [dut_register_write_2 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_2 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h2
  · rw [reference_load_register_3 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 3
    · rw [dut_register_write_3 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_3 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h3
  · rw [reference_load_register_4 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 4
    · rw [dut_register_write_4 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_4 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h4
  · rw [reference_load_register_5 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 5
    · rw [dut_register_write_5 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_5 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h5
  · rw [reference_load_register_6 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 6
    · rw [dut_register_write_6 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_6 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h6
  · rw [reference_load_register_7 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 7
    · rw [dut_register_write_7 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_7 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h7
  · rw [reference_load_register_8 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 8
    · rw [dut_register_write_8 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_8 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h8
  · rw [reference_load_register_9 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 9
    · rw [dut_register_write_9 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_9 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h9
  · rw [reference_load_register_10 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 10
    · rw [dut_register_write_10 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_10 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h10
  · rw [reference_load_register_11 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 11
    · rw [dut_register_write_11 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_11 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h11
  · rw [reference_load_register_12 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 12
    · rw [dut_register_write_12 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_12 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h12
  · rw [reference_load_register_13 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 13
    · rw [dut_register_write_13 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_13 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h13
  · rw [reference_load_register_14 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 14
    · rw [dut_register_write_14 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_14 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h14
  · rw [reference_load_register_15 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 15
    · rw [dut_register_write_15 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_15 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h15
  · rw [reference_load_register_16 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 16
    · rw [dut_register_write_16 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_16 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h16
  · rw [reference_load_register_17 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 17
    · rw [dut_register_write_17 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_17 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h17
  · rw [reference_load_register_18 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 18
    · rw [dut_register_write_18 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_18 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h18
  · rw [reference_load_register_19 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 19
    · rw [dut_register_write_19 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_19 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h19
  · rw [reference_load_register_20 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 20
    · rw [dut_register_write_20 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_20 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h20
  · rw [reference_load_register_21 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 21
    · rw [dut_register_write_21 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_21 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h21
  · rw [reference_load_register_22 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 22
    · rw [dut_register_write_22 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_22 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h22
  · rw [reference_load_register_23 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 23
    · rw [dut_register_write_23 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_23 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h23
  · rw [reference_load_register_24 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 24
    · rw [dut_register_write_24 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_24 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h24
  · rw [reference_load_register_25 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 25
    · rw [dut_register_write_25 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_25 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h25
  · rw [reference_load_register_26 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 26
    · rw [dut_register_write_26 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_26 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h26
  · rw [reference_load_register_27 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 27
    · rw [dut_register_write_27 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_27 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h27
  · rw [reference_load_register_28 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 28
    · rw [dut_register_write_28 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_28 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h28
  · rw [reference_load_register_29 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 29
    · rw [dut_register_write_29 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_29 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h29
  · rw [reference_load_register_30 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 30
    · rw [dut_register_write_30 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_30 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h30
  · rw [reference_load_register_31 s i operation load reset commit immediate targetAligned]
    by_cases dest : v11465 s i = 31
    · rw [dut_register_write_31 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_31 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h31


#print axioms load_registers_aligned_step
end NutShellProofs
