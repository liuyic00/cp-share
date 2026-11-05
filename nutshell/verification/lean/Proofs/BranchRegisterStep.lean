import Proofs.ReferenceBranchRegisters
import Proofs.ReferenceAddi
namespace NutShellProofs
open nNutCore

theorem branch_match_low32 (operation : BranchOp) (instr : BitVec 64)
    (matched : IsBranch operation instr) :
    BitVec.extractLsb' 0 32 instr &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32 := by
  have low := congrArg (BitVec.extractLsb' 0 32) matched
  cases operation <;> simpa only [BitVec.extractLsb'_and] using low

theorem reference_branch_hold_1 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1440_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = s.g45.r1440_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_1 s i reset matched
  | bne => exact reference_branch_bne_hold_1 s i reset matched
  | blt => exact reference_branch_blt_hold_1 s i reset matched
  | bge => exact reference_branch_bge_hold_1 s i reset matched
  | bltu => exact reference_branch_bltu_hold_1 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_1 s i reset matched
theorem reference_branch_hold_2 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1441_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = s.g45.r1441_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_2 s i reset matched
  | bne => exact reference_branch_bne_hold_2 s i reset matched
  | blt => exact reference_branch_blt_hold_2 s i reset matched
  | bge => exact reference_branch_bge_hold_2 s i reset matched
  | bltu => exact reference_branch_bltu_hold_2 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_2 s i reset matched
theorem reference_branch_hold_3 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1442_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = s.g45.r1442_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_3 s i reset matched
  | bne => exact reference_branch_bne_hold_3 s i reset matched
  | blt => exact reference_branch_blt_hold_3 s i reset matched
  | bge => exact reference_branch_bge_hold_3 s i reset matched
  | bltu => exact reference_branch_bltu_hold_3 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_3 s i reset matched
theorem reference_branch_hold_4 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1443_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = s.g45.r1443_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_4 s i reset matched
  | bne => exact reference_branch_bne_hold_4 s i reset matched
  | blt => exact reference_branch_blt_hold_4 s i reset matched
  | bge => exact reference_branch_bge_hold_4 s i reset matched
  | bltu => exact reference_branch_bltu_hold_4 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_4 s i reset matched
theorem reference_branch_hold_5 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1444_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = s.g45.r1444_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_5 s i reset matched
  | bne => exact reference_branch_bne_hold_5 s i reset matched
  | blt => exact reference_branch_blt_hold_5 s i reset matched
  | bge => exact reference_branch_bge_hold_5 s i reset matched
  | bltu => exact reference_branch_bltu_hold_5 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_5 s i reset matched
theorem reference_branch_hold_6 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1445_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = s.g45.r1445_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_6 s i reset matched
  | bne => exact reference_branch_bne_hold_6 s i reset matched
  | blt => exact reference_branch_blt_hold_6 s i reset matched
  | bge => exact reference_branch_bge_hold_6 s i reset matched
  | bltu => exact reference_branch_bltu_hold_6 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_6 s i reset matched
theorem reference_branch_hold_7 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1446_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = s.g45.r1446_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_7 s i reset matched
  | bne => exact reference_branch_bne_hold_7 s i reset matched
  | blt => exact reference_branch_blt_hold_7 s i reset matched
  | bge => exact reference_branch_bge_hold_7 s i reset matched
  | bltu => exact reference_branch_bltu_hold_7 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_7 s i reset matched
theorem reference_branch_hold_8 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1447_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = s.g45.r1447_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_8 s i reset matched
  | bne => exact reference_branch_bne_hold_8 s i reset matched
  | blt => exact reference_branch_blt_hold_8 s i reset matched
  | bge => exact reference_branch_bge_hold_8 s i reset matched
  | bltu => exact reference_branch_bltu_hold_8 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_8 s i reset matched
theorem reference_branch_hold_9 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1448_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = s.g45.r1448_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_9 s i reset matched
  | bne => exact reference_branch_bne_hold_9 s i reset matched
  | blt => exact reference_branch_blt_hold_9 s i reset matched
  | bge => exact reference_branch_bge_hold_9 s i reset matched
  | bltu => exact reference_branch_bltu_hold_9 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_9 s i reset matched
theorem reference_branch_hold_10 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1449_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = s.g45.r1449_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_10 s i reset matched
  | bne => exact reference_branch_bne_hold_10 s i reset matched
  | blt => exact reference_branch_blt_hold_10 s i reset matched
  | bge => exact reference_branch_bge_hold_10 s i reset matched
  | bltu => exact reference_branch_bltu_hold_10 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_10 s i reset matched
theorem reference_branch_hold_11 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1450_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = s.g45.r1450_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_11 s i reset matched
  | bne => exact reference_branch_bne_hold_11 s i reset matched
  | blt => exact reference_branch_blt_hold_11 s i reset matched
  | bge => exact reference_branch_bge_hold_11 s i reset matched
  | bltu => exact reference_branch_bltu_hold_11 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_11 s i reset matched
theorem reference_branch_hold_12 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1451_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = s.g45.r1451_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_12 s i reset matched
  | bne => exact reference_branch_bne_hold_12 s i reset matched
  | blt => exact reference_branch_blt_hold_12 s i reset matched
  | bge => exact reference_branch_bge_hold_12 s i reset matched
  | bltu => exact reference_branch_bltu_hold_12 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_12 s i reset matched
theorem reference_branch_hold_13 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1452_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = s.g45.r1452_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_13 s i reset matched
  | bne => exact reference_branch_bne_hold_13 s i reset matched
  | blt => exact reference_branch_blt_hold_13 s i reset matched
  | bge => exact reference_branch_bge_hold_13 s i reset matched
  | bltu => exact reference_branch_bltu_hold_13 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_13 s i reset matched
theorem reference_branch_hold_14 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1453_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = s.g45.r1453_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_14 s i reset matched
  | bne => exact reference_branch_bne_hold_14 s i reset matched
  | blt => exact reference_branch_blt_hold_14 s i reset matched
  | bge => exact reference_branch_bge_hold_14 s i reset matched
  | bltu => exact reference_branch_bltu_hold_14 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_14 s i reset matched
theorem reference_branch_hold_15 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1454_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = s.g45.r1454_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_15 s i reset matched
  | bne => exact reference_branch_bne_hold_15 s i reset matched
  | blt => exact reference_branch_blt_hold_15 s i reset matched
  | bge => exact reference_branch_bge_hold_15 s i reset matched
  | bltu => exact reference_branch_bltu_hold_15 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_15 s i reset matched
theorem reference_branch_hold_16 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1455_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = s.g45.r1455_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_16 s i reset matched
  | bne => exact reference_branch_bne_hold_16 s i reset matched
  | blt => exact reference_branch_blt_hold_16 s i reset matched
  | bge => exact reference_branch_bge_hold_16 s i reset matched
  | bltu => exact reference_branch_bltu_hold_16 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_16 s i reset matched
theorem reference_branch_hold_17 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1456_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = s.g45.r1456_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_17 s i reset matched
  | bne => exact reference_branch_bne_hold_17 s i reset matched
  | blt => exact reference_branch_blt_hold_17 s i reset matched
  | bge => exact reference_branch_bge_hold_17 s i reset matched
  | bltu => exact reference_branch_bltu_hold_17 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_17 s i reset matched
theorem reference_branch_hold_18 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1457_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = s.g45.r1457_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_18 s i reset matched
  | bne => exact reference_branch_bne_hold_18 s i reset matched
  | blt => exact reference_branch_blt_hold_18 s i reset matched
  | bge => exact reference_branch_bge_hold_18 s i reset matched
  | bltu => exact reference_branch_bltu_hold_18 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_18 s i reset matched
theorem reference_branch_hold_19 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1458_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = s.g45.r1458_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_19 s i reset matched
  | bne => exact reference_branch_bne_hold_19 s i reset matched
  | blt => exact reference_branch_blt_hold_19 s i reset matched
  | bge => exact reference_branch_bge_hold_19 s i reset matched
  | bltu => exact reference_branch_bltu_hold_19 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_19 s i reset matched
theorem reference_branch_hold_20 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1459_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = s.g45.r1459_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_20 s i reset matched
  | bne => exact reference_branch_bne_hold_20 s i reset matched
  | blt => exact reference_branch_blt_hold_20 s i reset matched
  | bge => exact reference_branch_bge_hold_20 s i reset matched
  | bltu => exact reference_branch_bltu_hold_20 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_20 s i reset matched
theorem reference_branch_hold_21 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1460_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = s.g45.r1460_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_21 s i reset matched
  | bne => exact reference_branch_bne_hold_21 s i reset matched
  | blt => exact reference_branch_blt_hold_21 s i reset matched
  | bge => exact reference_branch_bge_hold_21 s i reset matched
  | bltu => exact reference_branch_bltu_hold_21 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_21 s i reset matched
theorem reference_branch_hold_22 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1461_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = s.g45.r1461_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_22 s i reset matched
  | bne => exact reference_branch_bne_hold_22 s i reset matched
  | blt => exact reference_branch_blt_hold_22 s i reset matched
  | bge => exact reference_branch_bge_hold_22 s i reset matched
  | bltu => exact reference_branch_bltu_hold_22 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_22 s i reset matched
theorem reference_branch_hold_23 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1462_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = s.g45.r1462_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_23 s i reset matched
  | bne => exact reference_branch_bne_hold_23 s i reset matched
  | blt => exact reference_branch_blt_hold_23 s i reset matched
  | bge => exact reference_branch_bge_hold_23 s i reset matched
  | bltu => exact reference_branch_bltu_hold_23 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_23 s i reset matched
theorem reference_branch_hold_24 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1463_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = s.g45.r1463_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_24 s i reset matched
  | bne => exact reference_branch_bne_hold_24 s i reset matched
  | blt => exact reference_branch_blt_hold_24 s i reset matched
  | bge => exact reference_branch_bge_hold_24 s i reset matched
  | bltu => exact reference_branch_bltu_hold_24 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_24 s i reset matched
theorem reference_branch_hold_25 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1464_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = s.g45.r1464_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_25 s i reset matched
  | bne => exact reference_branch_bne_hold_25 s i reset matched
  | blt => exact reference_branch_blt_hold_25 s i reset matched
  | bge => exact reference_branch_bge_hold_25 s i reset matched
  | bltu => exact reference_branch_bltu_hold_25 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_25 s i reset matched
theorem reference_branch_hold_26 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1465_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = s.g45.r1465_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_26 s i reset matched
  | bne => exact reference_branch_bne_hold_26 s i reset matched
  | blt => exact reference_branch_blt_hold_26 s i reset matched
  | bge => exact reference_branch_bge_hold_26 s i reset matched
  | bltu => exact reference_branch_bltu_hold_26 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_26 s i reset matched
theorem reference_branch_hold_27 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1466_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = s.g45.r1466_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_27 s i reset matched
  | bne => exact reference_branch_bne_hold_27 s i reset matched
  | blt => exact reference_branch_blt_hold_27 s i reset matched
  | bge => exact reference_branch_bge_hold_27 s i reset matched
  | bltu => exact reference_branch_bltu_hold_27 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_27 s i reset matched
theorem reference_branch_hold_28 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1467_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = s.g45.r1467_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_28 s i reset matched
  | bne => exact reference_branch_bne_hold_28 s i reset matched
  | blt => exact reference_branch_blt_hold_28 s i reset matched
  | bge => exact reference_branch_bge_hold_28 s i reset matched
  | bltu => exact reference_branch_bltu_hold_28 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_28 s i reset matched
theorem reference_branch_hold_29 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1468_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = s.g45.r1468_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_29 s i reset matched
  | bne => exact reference_branch_bne_hold_29 s i reset matched
  | blt => exact reference_branch_blt_hold_29 s i reset matched
  | bge => exact reference_branch_bge_hold_29 s i reset matched
  | bltu => exact reference_branch_bltu_hold_29 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_29 s i reset matched
theorem reference_branch_hold_30 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1469_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = s.g45.r1469_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_30 s i reset matched
  | bne => exact reference_branch_bne_hold_30 s i reset matched
  | blt => exact reference_branch_blt_hold_30 s i reset matched
  | bge => exact reference_branch_bge_hold_30 s i reset matched
  | bltu => exact reference_branch_bltu_hold_30 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_30 s i reset matched
theorem reference_branch_hold_31 (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    (step s i).g45.r1470_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = s.g45.r1470_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 := by
  cases operation with
  | beq => exact reference_branch_beq_hold_31 s i reset matched
  | bne => exact reference_branch_bne_hold_31 s i reset matched
  | blt => exact reference_branch_blt_hold_31 s i reset matched
  | bge => exact reference_branch_bge_hold_31 s i reset matched
  | bltu => exact reference_branch_bltu_hold_31 s i reset matched
  | bgeu => exact reference_branch_bgeu_hold_31 s i reset matched

theorem branch_registers_aligned_run_step (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    ArchitecturalRegistersAligned (run initial inputs (t + 3)) := by
  have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&&
      operation.mask.setWidth 32 = operation.encoding.setWidth 32 := by
    have instr := committed_reference_instruction
      (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit
    exact (congrArg (fun x => x &&& operation.mask.setWidth 32) instr).trans
      (branch_match_low32 operation _ matched)
  have disabled := branch_writeback_disabled_run initial inputs reset t operation unit matched
  change ArchitecturalRegistersAligned (step (run initial inputs (t + 2)) (inputs (t + 2)))
  simpa only [ArchitecturalRegistersAligned,
    dut_register_disabled_1 _ _ currentReset disabled, reference_branch_hold_1 _ _ operation currentReset low,
    dut_register_disabled_2 _ _ currentReset disabled, reference_branch_hold_2 _ _ operation currentReset low,
    dut_register_disabled_3 _ _ currentReset disabled, reference_branch_hold_3 _ _ operation currentReset low,
    dut_register_disabled_4 _ _ currentReset disabled, reference_branch_hold_4 _ _ operation currentReset low,
    dut_register_disabled_5 _ _ currentReset disabled, reference_branch_hold_5 _ _ operation currentReset low,
    dut_register_disabled_6 _ _ currentReset disabled, reference_branch_hold_6 _ _ operation currentReset low,
    dut_register_disabled_7 _ _ currentReset disabled, reference_branch_hold_7 _ _ operation currentReset low,
    dut_register_disabled_8 _ _ currentReset disabled, reference_branch_hold_8 _ _ operation currentReset low,
    dut_register_disabled_9 _ _ currentReset disabled, reference_branch_hold_9 _ _ operation currentReset low,
    dut_register_disabled_10 _ _ currentReset disabled, reference_branch_hold_10 _ _ operation currentReset low,
    dut_register_disabled_11 _ _ currentReset disabled, reference_branch_hold_11 _ _ operation currentReset low,
    dut_register_disabled_12 _ _ currentReset disabled, reference_branch_hold_12 _ _ operation currentReset low,
    dut_register_disabled_13 _ _ currentReset disabled, reference_branch_hold_13 _ _ operation currentReset low,
    dut_register_disabled_14 _ _ currentReset disabled, reference_branch_hold_14 _ _ operation currentReset low,
    dut_register_disabled_15 _ _ currentReset disabled, reference_branch_hold_15 _ _ operation currentReset low,
    dut_register_disabled_16 _ _ currentReset disabled, reference_branch_hold_16 _ _ operation currentReset low,
    dut_register_disabled_17 _ _ currentReset disabled, reference_branch_hold_17 _ _ operation currentReset low,
    dut_register_disabled_18 _ _ currentReset disabled, reference_branch_hold_18 _ _ operation currentReset low,
    dut_register_disabled_19 _ _ currentReset disabled, reference_branch_hold_19 _ _ operation currentReset low,
    dut_register_disabled_20 _ _ currentReset disabled, reference_branch_hold_20 _ _ operation currentReset low,
    dut_register_disabled_21 _ _ currentReset disabled, reference_branch_hold_21 _ _ operation currentReset low,
    dut_register_disabled_22 _ _ currentReset disabled, reference_branch_hold_22 _ _ operation currentReset low,
    dut_register_disabled_23 _ _ currentReset disabled, reference_branch_hold_23 _ _ operation currentReset low,
    dut_register_disabled_24 _ _ currentReset disabled, reference_branch_hold_24 _ _ operation currentReset low,
    dut_register_disabled_25 _ _ currentReset disabled, reference_branch_hold_25 _ _ operation currentReset low,
    dut_register_disabled_26 _ _ currentReset disabled, reference_branch_hold_26 _ _ operation currentReset low,
    dut_register_disabled_27 _ _ currentReset disabled, reference_branch_hold_27 _ _ operation currentReset low,
    dut_register_disabled_28 _ _ currentReset disabled, reference_branch_hold_28 _ _ operation currentReset low,
    dut_register_disabled_29 _ _ currentReset disabled, reference_branch_hold_29 _ _ operation currentReset low,
    dut_register_disabled_30 _ _ currentReset disabled, reference_branch_hold_30 _ _ operation currentReset low,
    dut_register_disabled_31 _ _ currentReset disabled, reference_branch_hold_31 _ _ operation currentReset low] using aligned

#print axioms branch_registers_aligned_run_step
end NutShellProofs
