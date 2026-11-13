import Proofs.MulDivCheckedTrace

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

def holdInput : Inputs :=
  { nreset := 0, nio_5Freq_5Fvalid := 0, nio_5Freq_5Fbits_5Ffn := 0,
    nio_5Freq_5Fbits_5Fdw := 0, nio_5Freq_5Fbits_5Fin1 := 0, nio_5Freq_5Fbits_5Fin2 := 0,
    nio_5Freq_5Fbits_5Ftag := 0, nio_5Fkill := 0, nio_5Fresp_5Fready := 0 }

theorem held_pending (s : State) (pending : s.r9_ncontractPending = 1) :
    (step s holdInput).r9_ncontractPending = 1 := by
  rw [pending_transition]
  simp [holdInput, v2, pending]

theorem held_trace (s : State) (i : Inputs) (pending : s.r9_ncontractPending = 1)
    (response : v38 s i = 1) (n : Nat) :
    (run s (fun _ => holdInput) n).r9_ncontractPending = 1 ∧
    v38 (run s (fun _ => holdInput) n) holdInput = 1 ∧
    coreState (run s (fun _ => holdInput) n) = coreState s := by
  induction n with
  | zero => exact ⟨pending, response, rfl⟩
  | succ n ih =>
    refine ⟨held_pending _ ih.1, ?_, ?_⟩
    · exact (stalled_output _ holdInput holdInput ih.2.1 rfl rfl rfl).1
    · exact (stalled_core _ holdInput ih.2.1 rfl rfl rfl).trans ih.2.2

/-- Extend a finite observed prefix by retaining the completed response. -/
def holdAfter (inputs : Nat → Inputs) (finish : Nat) (t : Nat) : Inputs :=
  if t < finish then inputs t else holdInput

theorem hold_after_prefix (s : State) (inputs : Nat → Inputs) (finish n : Nat)
    (within : n ≤ finish) : run s (holdAfter inputs finish) n = run s inputs n := by
  apply run_congr
  intro t bound
  simp [holdAfter, show t < finish by omega]

theorem hold_after_suffix (s : State) (inputs : Nat → Inputs) (finish n : Nat) :
    run s (holdAfter inputs finish) (finish + n) =
      run (run s inputs finish) (fun _ => holdInput) n := by
  rw [run_offset, hold_after_prefix s inputs finish finish (by omega)]
  apply run_congr
  intro t bound
  simp [holdAfter, show ¬finish + t < finish by omega]

theorem hold_after_stable (s : State) (inputs : Nat → Inputs) (finish n : Nat)
    (pending : (run s inputs finish).r9_ncontractPending = 1)
    (response : v38 (run s inputs finish) (inputs finish) = 1) :
    coreState (run s (holdAfter inputs finish) (finish + n)) = coreState (run s inputs finish) := by
  rw [hold_after_suffix]
  exact (held_trace _ (inputs finish) pending response n).2.2

end HierarchicalMulDivChecked
