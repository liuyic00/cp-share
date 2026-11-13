import Proofs.MulDivCheckedCore
import Std.Tactic

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

def TagInvariant (s : State) : Prop :=
  s.r9_ncontractPending = 1 → s.r2_nreq_5Ftag = s.r15_ncontractTag

theorem tag_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    TagInvariant (step s i) := by
  simp [TagInvariant, step, eval_eq_spec, evalSpec, reset, v8]

theorem tag_preserved (s : State) (i : Inputs) (inv : TagInvariant s) :
    TagInvariant (step s i) := by
  unfold TagInvariant at inv ⊢
  simp only [step, eval_eq_spec, evalSpec, v8, v163, v162, v173, v63]
  bv_decide

theorem tag_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    TagInvariant (run (step s resetInput) inputs n) := by
  induction n with
  | zero => exact tag_reset s resetInput reset
  | succ n ih => exact tag_preserved _ _ ih

theorem tag_check (s : State) (i : Inputs) (inv : TagInvariant s) :
    v267 s i ≠ 1 ∨ v266 s i = 1 := by
  unfold TagInvariant at inv
  simp only [v267, v265, v259, v266]
  bv_decide

end HierarchicalMulDivChecked
