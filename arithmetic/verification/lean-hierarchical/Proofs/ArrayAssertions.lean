import Proofs.ArrayInvariant
import Proofs.ArrayHolding
import Proofs.ArrayComposition

namespace HierarchicalArray
open DesignnArrayMulDataModule.nArrayMulDataModule

private theorem enabled_checks (value expected previous : BitVec 130)
    (known holding reset : BitVec 1)
    (correct : known = 1 → value = expected)
    (held : holding = 1 → value = previous) :
    ([decide (known &&& (reset ^^^ 1) ≠ 1 ∨ (if value = expected then (1 : BitVec 1) else 0) = 1),
      decide (holding &&& (reset ^^^ 1) ≠ 1 ∨ (if value = previous then (1 : BitVec 1) else 0) = 1)] :
      List Bool).all id = true := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq,
    Bool.and_eq_true, decide_eq_true_eq]
  bv_decide

theorem local_asserts_of_invariants (s : State) (i : Inputs)
    (pipeline : PipelineInvariant s) (holding : HoldingInvariant s) :
    localAsserts s i := by
  have correct := pipeline.2 i
  have held := holding i
  have output : (observe s i).nio_5Fresult = v5371 s i := by
    simp only [observe, eval_eq_spec]
    rfl
  rw [output] at correct held
  unfold monitor at correct
  unfold localAsserts
  simp only [v5376, v5375, v5374, v5378, v5377, v3021]
  exact enabled_checks _ _ _ _ _ _ correct held

/-- All local and descendant assertions follow by reusing the compressor
    contracts and the two state invariants. -/
theorem asserts_of_invariants (s : State) (i : Inputs)
    (pipeline : PipelineInvariant s) (holding : HoldingInvariant s) : asserts s i :=
  asserts_from_pipeline s i (local_asserts_of_invariants s i pipeline holding)

theorem invariants_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    PipelineInvariant (run (step s resetInput) inputs n) ∧
    HoldingInvariant (run (step s resetInput) inputs n) := by
  induction n with
  | zero => exact ⟨pipeline_reset s resetInput reset, holding_after_step s resetInput⟩
  | succ n ih =>
    exact ⟨pipeline_preserved _ _ ih.1, holding_after_step _ _⟩

theorem asserts_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    asserts (run (step s resetInput) inputs n) (inputs n) := by
  obtain ⟨pipeline, holding⟩ := invariants_after_reset s resetInput reset inputs n
  exact asserts_of_invariants _ _ pipeline holding

end HierarchicalArray
