import Proofs.PipelineControl
namespace NutShellProofs
open nNutCore

theorem held_execute_excludes_writeback (s : State) (i next : Inputs)
    (valid : v6 (step s i) next = 1) (noCapture : v24283 s i ≠ 1) :
    v9 (step s i) next = 0 := by
  rcases BitVec.eq_zero_or_eq_one (v9 (step s i) next) with zero | one
  · exact zero
  · have done : v24278 s i = 1 := by
      change v11492 s i &&& v11702 s i = 1
      rw [BitVec.and_comm]
      exact commit_requires_capture s i next one
    have idle : v24277 s i ≠ 1 := noCapture
    change v24282 s i = 1 at valid
    simp only [v24282, v24281, v24280, idle, ↓reduceIte, v24279, done] at valid
    simp [v24] at valid

theorem dut_read_without_commit (s : State) (i next : Inputs) (addr : BitVec 5)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 0) :
    dutRead.v25201 (step s i) next addr = dutRead.v25201 s i addr := by
  have noWrite : v11462 s i = 0 := by simp [v11462, v11461, v11460, commit]
  rw [dut_read_step s i next addr reset]
  by_cases zero : addr = 0
  · rw [if_pos zero, zero, dutRead.read_0]
  · rw [if_neg zero, if_neg (by simp [noWrite])]

def RegisterOperand1Aligned (s : State) : Prop :=
  ∀ (i next : Inputs), v6 s i = 1 → s.g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = 0 →
    i.g0.nreset = 0 → v23 s i = 0 →
    s.g48.r1564_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc1 = dutRead.v25201 (step s i) next s.g48.r1555_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc1

theorem register_operand_1_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    RegisterOperand1Aligned (step s i) := by
  intro next later valid
  rw [execute_valid_reset s i next reset] at valid
  contradiction

theorem register_operand_1_step (s : State) (i : Inputs)
    (scoreboard : ExecuteDestinationBusy s) (old : RegisterOperand1Aligned s) :
    RegisterOperand1Aligned (step s i) := by
  intro next later valid nextKind nextReset nextFlush
  obtain ⟨reset, flush⟩ := next_valid_controls s i next valid
  by_cases fire : v24283 s i = 1
  · have capturedKind : (step s i).g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = v24881 s i := by
      change v24883 s i = v24881 s i
      simp [v24883, fire, v24882]
    have capturedAddr : (step s i).g48.r1555_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc1 = v11723 s i := by
      change v24930 s i = v11723 s i
      simp [v24930, fire, v24929]
    rw [capturedAddr]
    exact issued_operand_1_after_older_writeback s i next later scoreboard fire
      (capturedKind.symm.trans nextKind) reset nextReset flush nextFlush
  · have heldKind : (step s i).g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = s.g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type := by
      change v24883 s i = _
      rw [v24883, if_neg fire]
    have heldAddr : (step s i).g48.r1555_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc1 = s.g48.r1555_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc1 := by
      change v24930 s i = _
      rw [v24930, if_neg fire]
    have heldData : (step s i).g48.r1564_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc1 = s.g48.r1564_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc1 := by
      change v25206 s i = _
      rw [v25206, if_neg fire]
    have prior := execute_valid_backward s i next valid fire
    have noCommit := held_execute_excludes_writeback s i next valid fire
    rw [heldAddr, heldData, dut_read_without_commit (step s i) next later _ nextReset noCommit]
    exact old i next prior (heldKind.symm.trans nextKind) reset flush

theorem register_operand_1_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    RegisterOperand1Aligned (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact register_operand_1_reset initial (inputs 0) reset
  | succ t ih =>
    exact register_operand_1_step _ _ (execute_busy_run initial inputs reset t) ih

#print axioms register_operand_1_run
def RegisterOperand2Aligned (s : State) : Prop :=
  ∀ (i next : Inputs), v6 s i = 1 → s.g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = 0 →
    i.g0.nreset = 0 → v23 s i = 0 →
    s.g48.r1565_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc2 = dutRead.v25201 (step s i) next s.g48.r1556_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc2

theorem register_operand_2_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    RegisterOperand2Aligned (step s i) := by
  intro next later valid
  rw [execute_valid_reset s i next reset] at valid
  contradiction

theorem register_operand_2_step (s : State) (i : Inputs)
    (scoreboard : ExecuteDestinationBusy s) (old : RegisterOperand2Aligned s) :
    RegisterOperand2Aligned (step s i) := by
  intro next later valid nextKind nextReset nextFlush
  obtain ⟨reset, flush⟩ := next_valid_controls s i next valid
  by_cases fire : v24283 s i = 1
  · have capturedKind : (step s i).g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = v24896 s i := by
      change v24898 s i = v24896 s i
      simp [v24898, fire, v24897]
    have capturedAddr : (step s i).g48.r1556_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc2 = v11765 s i := by
      change v24932 s i = v11765 s i
      simp [v24932, fire, v24931]
    rw [capturedAddr]
    exact issued_operand_2_after_older_writeback s i next later scoreboard fire
      (capturedKind.symm.trans nextKind) reset nextReset flush nextFlush
  · have heldKind : (step s i).g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = s.g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type := by
      change v24898 s i = _
      rw [v24898, if_neg fire]
    have heldAddr : (step s i).g48.r1556_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc2 = s.g48.r1556_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfSrc2 := by
      change v24932 s i = _
      rw [v24932, if_neg fire]
    have heldData : (step s i).g48.r1565_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc2 = s.g48.r1565_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc2 := by
      change v25325 s i = _
      rw [v25325, if_neg fire]
    have prior := execute_valid_backward s i next valid fire
    have noCommit := held_execute_excludes_writeback s i next valid fire
    rw [heldAddr, heldData, dut_read_without_commit (step s i) next later _ nextReset noCommit]
    exact old i next prior (heldKind.symm.trans nextKind) reset flush

theorem register_operand_2_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    RegisterOperand2Aligned (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact register_operand_2_reset initial (inputs 0) reset
  | succ t ih =>
    exact register_operand_2_step _ _ (execute_busy_run initial inputs reset t) ih

#print axioms register_operand_2_run
end NutShellProofs
