import Proofs.NonregisterSourceDecode
import Proofs.IssueReadiness
namespace NutShellProofs
open nNutCore

def extendOperandPC (pc : BitVec 39) : BitVec 64 :=
  (if BitVec.extractLsb' 38 1 pc = 1 then BitVec.ofNat 25 33554431 else 0) ++ pc


theorem nonregister_no_forward_1 (s : State) (i : Inputs)
    (queue : QueueNonregisterSources1Decoded s) (kind : v24881 s i = 1) :
    v11741 s i = 0 ∧ v11750 s i = 0 := by
  have zero := queue_selected_nonregister_source1 s i queue kind
  have noEx : v11741 s i ≠ 1 := fun h => (execute_forward_1_matches s i h).1 zero
  have noWb : v11750 s i ≠ 1 := fun h => (writeback_forward_1_matches s i h).1 zero
  exact ⟨(BitVec.eq_zero_or_eq_one _).resolve_right noEx, (BitVec.eq_zero_or_eq_one _).resolve_right noWb⟩

def NonregisterOperand1 (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 → s.g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = 1 →
    s.g48.r1564_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc1 = extendOperandPC (s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc)

theorem nonregister_operand_1_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    NonregisterOperand1 (step s i) := by
  intro valid
  change v6 (step s i) i = 1 at valid
  rw [execute_valid_reset s i i reset] at valid
  contradiction

theorem nonregister_operand_1_step (s : State) (i : Inputs)
    (queue : QueueNonregisterSources1Decoded s) (old : NonregisterOperand1 s) :
    NonregisterOperand1 (step s i) := by
  intro valid kind
  change v24883 s i = 1 at kind
  change v25206 s i = extendOperandPC (v24313 s i)
  by_cases fire : v24283 s i = 1
  · have sourceKind : v24881 s i = 1 := by simpa only [v24883, v24882, v24897, fire, ↓reduceIte] using kind
    obtain ⟨ex, wb⟩ := nonregister_no_forward_1 s i queue sourceKind
    have value := operand_1_pc s i sourceKind ex wb
    simp only [v25206, v24313, v24312, v25326, fire, ↓reduceIte]
    exact value
  · have sourceKind : s.g48.r1551_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc1Type = 1 := by simpa only [v24883, fire, ↓reduceIte] using kind
    simp only [v25206, v24313, fire, ↓reduceIte]
    exact old (execute_valid_backward s i i valid fire) sourceKind

theorem nonregister_operand_1_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    NonregisterOperand1 (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact nonregister_operand_1_reset initial (inputs 0) reset
  | succ t ih => exact nonregister_operand_1_step _ _ (nonregister_source1_decode_run initial inputs reset t).1 ih
#print axioms nonregister_operand_1_run

theorem nonregister_no_forward_2 (s : State) (i : Inputs)
    (queue : QueueNonregisterSources2Decoded s) (kind : v24896 s i = 1) :
    v11776 s i = 0 ∧ v11785 s i = 0 := by
  have zero := queue_selected_nonregister_source2 s i queue kind
  have noEx : v11776 s i ≠ 1 := fun h => (execute_forward_2_matches s i h).1 zero
  have noWb : v11785 s i ≠ 1 := fun h => (writeback_forward_2_matches s i h).1 zero
  exact ⟨(BitVec.eq_zero_or_eq_one _).resolve_right noEx, (BitVec.eq_zero_or_eq_one _).resolve_right noWb⟩

def NonregisterOperand2 (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 → s.g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = 1 →
    s.g48.r1565_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc2 =  (s.g48.r1566_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fimm)

theorem nonregister_operand_2_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    NonregisterOperand2 (step s i) := by
  intro valid
  change v6 (step s i) i = 1 at valid
  rw [execute_valid_reset s i i reset] at valid
  contradiction

theorem nonregister_operand_2_step (s : State) (i : Inputs)
    (queue : QueueNonregisterSources2Decoded s) (old : NonregisterOperand2 s) :
    NonregisterOperand2 (step s i) := by
  intro valid kind
  change v24898 s i = 1 at kind
  change v25325 s i =  (v25327 s i)
  by_cases fire : v24283 s i = 1
  · have sourceKind : v24896 s i = 1 := by simpa only [v24898, v24882, v24897, fire, ↓reduceIte] using kind
    obtain ⟨ex, wb⟩ := nonregister_no_forward_2 s i queue sourceKind
    have value := operand_2_immediate s i sourceKind ex wb
    simp only [v25325, v25327, v24312, v25326, fire, ↓reduceIte]
    exact value
  · have sourceKind : s.g48.r1552_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5Fsrc2Type = 1 := by simpa only [v24898, fire, ↓reduceIte] using kind
    simp only [v25325, v25327, fire, ↓reduceIte]
    exact old (execute_valid_backward s i i valid fire) sourceKind

theorem nonregister_operand_2_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    NonregisterOperand2 (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact nonregister_operand_2_reset initial (inputs 0) reset
  | succ t ih => exact nonregister_operand_2_step _ _ (nonregister_source2_decode_run initial inputs reset t).1 ih
#print axioms nonregister_operand_2_run
end NutShellProofs
