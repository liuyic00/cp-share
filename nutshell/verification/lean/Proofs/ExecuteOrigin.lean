import Proofs.OperandSelection
namespace NutShellProofs
open nNutCore
structure ExecutePayload where
  field0 : BitVec 64
  field1 : BitVec 39
  field2 : BitVec 39
  field3 : BitVec 39
  field4 : BitVec 1
  field5 : BitVec 1
  field6 : BitVec 1
  field7 : BitVec 1
  field8 : BitVec 1
  field9 : BitVec 1
  field10 : BitVec 1
  field11 : BitVec 1
  field12 : BitVec 1
  field13 : BitVec 1
  field14 : BitVec 1
  field15 : BitVec 1
  field16 : BitVec 1
  field17 : BitVec 1
  field18 : BitVec 1
  field19 : BitVec 1
  field20 : BitVec 1
  field21 : BitVec 1
  field22 : BitVec 1
  field23 : BitVec 1
  field24 : BitVec 1
  field25 : BitVec 1
  field26 : BitVec 1
  field27 : BitVec 1
  field28 : BitVec 1
  field29 : BitVec 1
  field30 : BitVec 1
  field31 : BitVec 1
  field32 : BitVec 1
  field33 : BitVec 1
  field34 : BitVec 4
  field35 : BitVec 1
  field36 : BitVec 1
  field37 : BitVec 64
  field38 : BitVec 1
  field39 : BitVec 1
  field40 : BitVec 1
  field41 : BitVec 3
  field42 : BitVec 7
  field43 : BitVec 5
  field44 : BitVec 5
  field45 : BitVec 1
  field46 : BitVec 5
  field47 : BitVec 1
  field48 : BitVec 1
  field49 : BitVec 1
  field50 : BitVec 1
  field51 : BitVec 1
  field52 : BitVec 64
  field53 : BitVec 64
  field54 : BitVec 64
def executePayload (s : State) : ExecutePayload :=
  ⟨s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr, s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc, s.g47.r1514_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpnpc, s.g47.r1515_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fredirect_5Ftarget, s.g47.r1516_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fredirect_5Frtype, s.g47.r1517_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fredirect_5Fvalid, s.g47.r1518_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F0, s.g47.r1519_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F1, s.g47.r1520_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F2, s.g47.r1521_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F3, s.g47.r1522_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F4, s.g47.r1523_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F5, s.g47.r1524_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F6, s.g47.r1525_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F7, s.g47.r1526_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F8, s.g47.r1527_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F9, s.g47.r1528_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F10, s.g47.r1529_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F11, s.g47.r1530_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F12, s.g47.r1531_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F13, s.g47.r1532_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F14, s.g47.r1533_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FexceptionVec_5F15, s.g47.r1534_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FintrVec_5F0, s.g47.r1535_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FintrVec_5F1, s.g48.r1536_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FintrVec_5F2, s.g48.r1537_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FintrVec_5F3, s.g48.r1538_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FintrVec_5F4, s.g48.r1539_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FintrVec_5F5, s.g48.r1540_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FintrVec_5F6, s.g48.r1541_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FintrVec_5F7, s.g48.r1542_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FintrVec_5F8, s.g48.r1543_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FintrVec_5F9, s.g48.r1544_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FintrVec_5F10, s.g48.r1545_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FintrVec_5F11, s.g48.r1546_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FbrIdx, s.g48.r1547_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FisRVC, s.g48.r1548_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FcrossPageIPFFix, s.g48.r1549_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Frunahead_5Fcheckpoint_5Fid, s.g48.r1550_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5FisBranch, s.g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type, s.g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type, s.g48.r1553_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FfuType, s.g48.r1554_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FfuOpType, s.g48.r1555_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc1, s.g48.r1556_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc2, s.g48.r1557_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfWen, s.g48.r1558_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfDest, s.g48.r1559_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FisNutCoreTrap, s.g48.r1560_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FisSrc1Forward, s.g48.r1561_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FisSrc2Forward, s.g48.r1562_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FnoSpecExec, s.g48.r1563_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FisBlocked, s.g48.r1564_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc1, s.g48.r1565_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc2, s.g48.r1566_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fimm⟩
theorem execute_payload_hold (s : State) (i : Inputs) (fire : v24283 s i ≠ 1) :
    executePayload (step s i) = executePayload s := by
  change ExecutePayload.mk (v24298 s i) (v24313 s i) (v24328 s i) (v24343 s i) (v24358 s i) (v24373 s i) (v24388 s i) (v24403 s i) (v24418 s i) (v24433 s i) (v24448 s i) (v24463 s i) (v24478 s i) (v24493 s i) (v24508 s i) (v24523 s i) (v24538 s i) (v24553 s i) (v24568 s i) (v24583 s i) (v24598 s i) (v24613 s i) (v24628 s i) (v24643 s i) (v24658 s i) (v24673 s i) (v24688 s i) (v24703 s i) (v24718 s i) (v24733 s i) (v24748 s i) (v24763 s i) (v24778 s i) (v24793 s i) (v24808 s i) (v24823 s i) (v24838 s i) (v24853 s i) (v24868 s i) (v24883 s i) (v24898 s i) (v24913 s i) (v24928 s i) (v24930 s i) (v24932 s i) (v24947 s i) (v24949 s i) (v24964 s i) (v24966 s i) (v24968 s i) (v24983 s i) (v24998 s i) (v25206 s i) (v25325 s i) (v25327 s i) = _
  simp only [v24298, v24313, v24328, v24343, v24358, v24373, v24388, v24403, v24418, v24433, v24448, v24463, v24478, v24493, v24508, v24523, v24538, v24553, v24568, v24583, v24598, v24613, v24628, v24643, v24658, v24673, v24688, v24703, v24718, v24733, v24748, v24763, v24778, v24793, v24808, v24823, v24838, v24853, v24868, v24883, v24898, v24913, v24928, v24930, v24932, v24947, v24949, v24964, v24966, v24968, v24983, v24998, v25206, v25325, v25327, fire, ↓reduceIte]
  rfl
theorem execute_valid_reset (s : State) (i next : Inputs) (reset : i.g0.nreset = 1) :
    v6 (step s i) next = 0 := by
  change v24282 s i = 0
  simp [v24282, v11455, v24, reset]

theorem execute_valid_backward (s : State) (i next : Inputs)
    (valid : v6 (step s i) next = 1) (fire : v24283 s i ≠ 1) :
    v6 s i = 1 := by
  have noCapture : v24277 s i ≠ 1 := fire
  change v24282 s i = 1 at valid
  unfold v24282 at valid
  split at valid
  · simp [v24] at valid
  · unfold v24281 at valid
    split at valid
    · simp [v24] at valid
    · simp only [v24280, noCapture, ↓reduceIte] at valid
      unfold v24279 at valid
      split at valid
      · simp [v24] at valid
      · exact valid

-- This tracks the complete EXU input bundle, not just its two data operands.
theorem execute_payload_origin (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    ∃ k, k < t + 1 ∧ v24283 (run initial inputs k) (inputs k) = 1 ∧
      executePayload (run initial inputs (t + 1)) =
        executePayload (step (run initial inputs k) (inputs k)) := by
  induction t with
  | zero =>
    have invalid := execute_valid_reset initial (inputs 0) (inputs 1) reset
    change v6 (run initial inputs 1) (inputs 1) = 0 at invalid
    rw [invalid] at valid
    contradiction
  | succ t ih =>
    by_cases fire : v24283 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
    · exact ⟨t + 1, by omega, fire, rfl⟩
    · have prior := execute_valid_backward _ _ _ valid fire
      obtain ⟨k, bound, captured, same⟩ := ih prior
      refine ⟨k, by omega, captured, ?_⟩
      exact (execute_payload_hold _ _ fire).trans same

#print axioms execute_payload_origin
end NutShellProofs
