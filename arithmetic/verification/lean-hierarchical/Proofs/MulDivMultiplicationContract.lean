import Proofs.MulDivWordResponse

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

def multiplicationLatency (i : Inputs) : Nat :=
  if i.nio_5Freq_5Fbits_5Ffn = 0#4 ∧ i.nio_5Freq_5Fbits_5Fdw = 0#1 then 33 else 65

def multiplicationSpecification (i : Inputs) : BitVec 64 :=
  if i.nio_5Freq_5Fbits_5Ffn = 0#4 then
    if i.nio_5Freq_5Fbits_5Fdw = 1 then i.nio_5Freq_5Fbits_5Fin1 * i.nio_5Freq_5Fbits_5Fin2
    else (i.nio_5Freq_5Fbits_5Fin1.setWidth 32 * i.nio_5Freq_5Fbits_5Fin2.setWidth 32).signExtend 64
  else highProductSpecification i

/-- All supported multiply requests, with word mode restricted to MULW. -/
theorem multiplication_accepted (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (legal : (inputs 0).nio_5Freq_5Fbits_5Ffn = 0#4 ∨
      ((inputs 0).nio_5Freq_5Fbits_5Fdw = 1 ∧
       ((inputs 0).nio_5Freq_5Fbits_5Ffn = 1#4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 2#4 ∨
        (inputs 0).nio_5Freq_5Fbits_5Ffn = 3#4)))
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    let n := multiplicationLatency (inputs 0)
    (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
    (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata = multiplicationSpecification (inputs 0) := by
  rcases legal with low | ⟨full, high⟩
  · by_cases full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1
    · simpa [multiplicationLatency, multiplicationSpecification, low, full] using
        low_product_accepted s inputs idle valid full low reset alive
    · have word : (inputs 0).nio_5Freq_5Fbits_5Fdw = 0#1 := by bv_decide
      simpa [multiplicationLatency, multiplicationSpecification, low, word] using
        word_product_accepted s inputs idle valid word low
          (by intro t h; exact reset t (by omega)) (by intro t h; exact alive t (by omega))
  · have notLow : (inputs 0).nio_5Freq_5Fbits_5Ffn ≠ 0#4 := by
      rcases high with h | h | h <;> rw [h] <;> decide
    simpa [multiplicationLatency, multiplicationSpecification, notLow] using
      high_product_accepted s inputs idle valid full high reset alive

#print axioms multiplication_accepted
end HierarchicalMulDiv
