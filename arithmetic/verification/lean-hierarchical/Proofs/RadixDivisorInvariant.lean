import Proofs.RadixHistory

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

def DivisorInvariant (s : State) : Prop :=
  s.r0_nstate ≠ 0 → s.r1_ndivBy0Reg = 0 → s.r5_nbReg ≠ 0

theorem divisor_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    DivisorInvariant (step s i) := by
  simp [DivisorInvariant, step, eval_eq_spec, evalSpec, reset, v0]

theorem divisor_preserved (s : State) (i : Inputs) (inv : DivisorInvariant s) :
    DivisorInvariant (step s i) := by
  unfold DivisorInvariant at inv ⊢
  simp only [step, eval_eq_spec, evalSpec, v0, v1, v2, v3, v4, v5, v6,
    v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19,
    v20, v21, v22, v23, v24, v48, v49, v53, v54, v55]
  bv_decide

theorem divisor_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    DivisorInvariant (run (step s resetInput) inputs n) := by
  induction n with
  | zero => exact divisor_reset s resetInput reset
  | succ n ih => exact divisor_preserved _ _ ih

theorem divisor_check (s : State) (i : Inputs) (inv : DivisorInvariant s) :
    (v422 s i) ≠ 1 ∨ (v421 s i) = 1 := by
  unfold DivisorInvariant at inv
  simp only [v422, v399, v11, v420, v22, v416, v421, v20]
  bv_decide

end HierarchicalRadix
