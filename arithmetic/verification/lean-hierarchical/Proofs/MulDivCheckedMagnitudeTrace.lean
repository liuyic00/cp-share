import Proofs.MulDivCheckedHoldTrace
import Proofs.MulDivCheckedSnapshots

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

/-- A pending completed response retains its uncorrected monitor magnitudes
    throughout an arbitrary interval without another captured request. -/
theorem pending_magnitudes_stable (s : State) (inputs : Nat → Inputs) (start finish : Nat)
    (pending : (run s inputs finish).r9_ncontractPending = 1)
    (noCapture : ∀ t, start ≤ t → t < finish → v2 (run s inputs t) (inputs t) ≠ 1)
    (response : v38 (run s inputs start) (inputs start) = 1)
    (t : Nat) (lower : start ≤ t) (upper : t ≤ finish) :
    v232 (run s inputs t) (inputs t) = v232 (run s inputs start) (inputs start) ∧
    v233 (run s inputs t) (inputs t) = v233 (run s inputs start) (inputs start) := by
  induction t with
  | zero =>
    have h : start = 0 := by omega
    subst start
    exact ⟨rfl, rfl⟩
  | succ t ih =>
    by_cases first : start = t + 1
    · subst start; exact ⟨rfl, rfl⟩
    · have previous := ih (by omega) (by omega)
      have valid := (pending_response_stable s inputs start finish pending noCapture
        response t (by omega) (by omega)).1
      have nextPending := pending_at s inputs start finish pending noCapture
        (t + 1) (by omega) upper
      have edge := terminal_magnitudes (run s inputs t) (inputs t) (inputs (t + 1))
        valid (pending_edge _ _ nextPending).1
      exact ⟨edge.1.trans previous.1, edge.2.trans previous.2⟩

theorem held_magnitudes (s : State) (i : Inputs) (pending : s.r9_ncontractPending = 1)
    (response : v38 s i = 1) (n : Nat) :
    v232 (run s (fun _ => holdInput) n) holdInput = v232 s i ∧
    v233 (run s (fun _ => holdInput) n) holdInput = v233 s i := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have valid := (held_trace s i pending response n).2.1
    have edge := terminal_magnitudes (run s (fun _ => holdInput) n)
      holdInput holdInput valid rfl
    exact ⟨edge.1.trans ih.1, edge.2.trans ih.2⟩

theorem hold_after_magnitudes (s : State) (inputs : Nat → Inputs) (finish n : Nat)
    (pending : (run s inputs finish).r9_ncontractPending = 1)
    (response : v38 (run s inputs finish) (inputs finish) = 1) :
    v232 (run s (holdAfter inputs finish) (finish + n)) (holdAfter inputs finish (finish + n)) =
      v232 (run s inputs finish) (inputs finish) ∧
    v233 (run s (holdAfter inputs finish) (finish + n)) (holdAfter inputs finish (finish + n)) =
      v233 (run s inputs finish) (inputs finish) := by
  rw [hold_after_suffix]
  exact held_magnitudes _ (inputs finish) pending response n

end HierarchicalMulDivChecked
