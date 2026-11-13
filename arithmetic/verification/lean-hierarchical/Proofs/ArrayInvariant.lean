import Proofs.ArrayValues

namespace HierarchicalArray
open DesignnArrayMulDataModule.nArrayMulDataModule

private theorem bit_cases (x : BitVec 1) : x = 0 ∨ x = 1 := by bv_decide

theorem signed_product_int (i : Inputs) :
    signedProduct i = BitVec.ofInt 130 (i.nio_5Fa.toInt * i.nio_5Fb.toInt) := by
  rw [BitVec.ofInt_mul]
  rfl

theorem first_value_transition (s : State) (i later : Inputs) :
    firstValue (step s i) later =
      if i.nio_5FregEnables_5F0 = 1 then signedProduct i else firstValue s i := by
  rcases bit_cases i.nio_5FregEnables_5F0 with h | h
  · simpa [h] using first_value_hold s i later h
  · simpa [h, signed_product_int] using first_value_capture s i later h

theorem output_value_transition (s : State) (i later : Inputs) :
    (observe (step s i) later).nio_5Fresult =
      if i.nio_5FregEnables_5F1 = 1 then firstValue s i else (observe s i).nio_5Fresult := by
  rcases bit_cases i.nio_5FregEnables_5F1 with h | h
  · simpa [h] using output_hold s i later h
  · simpa [h, firstValue] using output_after_transfer s i later h

/-- Valid monitor entries equal the corresponding data stage's value. -/
def PipelineInvariant (s : State) : Prop :=
  (∀ i, (monitor s).2.1 = 1 → firstValue s i = (monitor s).1) ∧
  (∀ i, (monitor s).2.2.2 = 1 → (observe s i).nio_5Fresult = (monitor s).2.2.1)

theorem pipeline_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    PipelineInvariant (step s i) := by
  unfold PipelineInvariant
  rw [monitor_transition]
  simp [reset]

theorem pipeline_preserved (s : State) (i : Inputs) (inv : PipelineInvariant s) :
    PipelineInvariant (step s i) := by
  rcases inv with ⟨first, result⟩
  unfold PipelineInvariant
  rw [monitor_transition]
  constructor
  · intro later valid
    rw [first_value_transition]
    rcases bit_cases i.nreset with reset | reset <;>
      rcases bit_cases i.nio_5FregEnables_5F0 with enable | enable <;>
      simp_all
  · intro later valid
    rw [output_value_transition]
    rcases bit_cases i.nreset with reset | reset <;>
      rcases bit_cases i.nio_5FregEnables_5F1 with enable | enable <;>
      simp_all

end HierarchicalArray
