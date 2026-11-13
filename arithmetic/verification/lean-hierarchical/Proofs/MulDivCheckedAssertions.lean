import Proofs.MulDivCheckedResultChecks
import Proofs.MulDivCheckedTimingChecks

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

def TimingInvariant (s : State) : Prop :=
  ∀ i, s.r9_ncontractPending = 1 →
    s.r10_ncontractAge.ule (expectedAge s) = true ∧
    (v38 s i = 1 ↔ s.r10_ncontractAge = expectedAge s)

def OutputInvariant (s : State) : Prop :=
  ∀ i, s.r9_ncontractPending = 1 → v38 s i = 1 → v187 s i = v258 s i

theorem output_check (s : State) (i : Inputs) (inv : OutputInvariant s) :
    v267 s i ≠ 1 ∨ v268 s i = 1 := by
  have h := inv i
  simp only [v267, v265, v259, v268]
  bv_decide

theorem asserts_of_invariants (s : State) (i : Inputs)
    (timing : TimingInvariant s) (tag : TagInvariant s) (output : OutputInvariant s)
    (magnitudes : MagnitudeInvariant s) (stall : StallInvariant s) : asserts s i := by
  have time := timing_checks_of_contract s i (timing i)
  have tags := tag_check s i tag
  have data := output_check s i output
  have division := magnitude_checks s i magnitudes
  have holding := stall_checks s i stall
  apply asserts_of_parts
  unfold localAsserts
  simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨time.1, time.2, tags, data, division.1, division.2.1,
    division.2.2.1, division.2.2.2, holding.1, holding.2.1, holding.2.2⟩

end HierarchicalMulDivChecked
