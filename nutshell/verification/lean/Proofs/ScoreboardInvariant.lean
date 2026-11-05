import Proofs.ScoreboardUpdate
import Proofs.ExecuteOrigin
namespace NutShellProofs
open nNutCore

def ExecuteDestinationBusy (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 →
  s.g48.r1557_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfWen = 1 →
  s.g48.r1558_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfDest ≠ 0 →
  s.g40.r1285_nbackend_5Fisu_5Fbusy.getLsbD
    s.g48.r1558_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfDest.toNat = true

theorem execute_busy_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    ExecuteDestinationBusy (step s i) := by
  intro valid
  have zero := execute_valid_reset s i i reset
  change v6 (step s i) i = 1 at valid
  rw [zero] at valid
  contradiction

theorem execute_busy_step (s : State) (i : Inputs) (old : ExecuteDestinationBusy s) :
    ExecuteDestinationBusy (step s i) := by
  intro valid write nonzero
  have nextValid : v6 (step s i) i = 1 := valid
  have reset : i.g0.nreset = 0 := by
    rcases BitVec.eq_zero_or_eq_one i.g0.nreset with h | h
    · exact h
    · rw [execute_valid_reset s i i h] at nextValid
      contradiction
  have flush : v11458 s i = 0 := by
    rcases BitVec.eq_zero_or_eq_one (v11458 s i) with h | h
    · exact h
    · have flushed : v24276 s i = 1 := h
      change v24282 s i = 1 at nextValid
      simp [v24282, v11455, reset, v24281, flushed, v24] at nextValid
  by_cases fire : v24283 s i = 1
  · have dest : (step s i).g48.r1558_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfDest = v11803 s i := by
      change v24949 s i = v11803 s i
      simp [v24949, fire, v24948]
    rw [dest] at nonzero ⊢
    exact scoreboard_issue_sets s i reset flush fire nonzero
  · have dest : (step s i).g48.r1558_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfDest =
        s.g48.r1558_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfDest := by
      change v24949 s i = _
      rw [v24949, if_neg fire]
    have wen : (step s i).g48.r1557_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfWen =
        s.g48.r1557_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfWen := by
      change v24947 s i = _
      rw [v24947, if_neg fire]
    rw [dest] at nonzero ⊢
    rw [wen] at write
    have prior := execute_valid_backward s i i nextValid fire
    have validWrite : v11478 s i = 1 := by
      simp [v11478, v11475, v11474, v11473, v11477, v11476, prior, write]
    exact scoreboard_execute_preserved s i reset flush validWrite nonzero (old prior write nonzero)

theorem execute_busy_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    ExecuteDestinationBusy (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact execute_busy_reset initial (inputs 0) reset
  | succ t ih => exact execute_busy_step _ _ ih

#print axioms execute_busy_run
end NutShellProofs
