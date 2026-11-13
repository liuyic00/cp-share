import Proofs.MulDivCheckedHistory
import Proofs.MulDivMulLow
import Proofs.MulDivMulWordProduct

namespace MulDivCheckedMulSpec
open nMulDiv

def specification (i : Inputs) : BitVec 64 :=
  if i.nio_5Freq_5Fbits_5Ffn = 0 then
    if i.nio_5Freq_5Fbits_5Fdw = 1 then MulDivMultiply.lowSpecification i else MulDivMultiply.wordSpecification i
  else if i.nio_5Freq_5Fbits_5Ffn = 3 then MulDivMultiply.unsignedHighSpecification i
  else MulDivMultiply.signedHighSpecification i

def total (i : Inputs) : Nat := if i.nio_5Freq_5Fbits_5Fdw = 1 then 65 else 33

def Legal (i : Inputs) : Prop := i.nio_5Freq_5Fbits_5Ffn < 4#4 ∧
  (i.nio_5Freq_5Fbits_5Ffn = 0 ∨ i.nio_5Freq_5Fbits_5Fdw = 1)

theorem accepted_result (s : State) (pins : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (pins 0).nio_5Freq_5Fvalid = 1) (legal : Legal (pins 0))
    (resets : ∀ t, t < total (pins 0) → (pins t).nreset = 0)
    (kills : ∀ t, t < total (pins 0) → (pins t).nio_5Fkill = 0) :
    (observe (run s pins (total (pins 0))) (pins (total (pins 0)))).nio_5Fresp_5Fbits_5Fdata =
      specification (pins 0) := by
  have range := legal.1
  have cases : (pins 0).nio_5Freq_5Fbits_5Ffn = 0 ∨ (pins 0).nio_5Freq_5Fbits_5Ffn = 1 ∨
      (pins 0).nio_5Freq_5Fbits_5Ffn = 2 ∨ (pins 0).nio_5Freq_5Fbits_5Ffn = 3 := by bv_decide
  rcases cases with op | op | op | op
  · by_cases full : (pins 0).nio_5Freq_5Fbits_5Fdw = 1
    · simpa [total, specification, op, full] using
        (MulDivMultiply.low_result s pins idle valid op full
          (by simpa [total, full] using resets) (by simpa [total, full] using kills)).2.1
    · have word : (pins 0).nio_5Freq_5Fbits_5Fdw = 0 := by bv_decide
      simpa [total, specification, op, word] using
        (MulDivMultiply.word_result s pins idle valid op word
          (by simpa [total, word] using resets) (by simpa [total, word] using kills)).2.1
  all_goals
    have full : (pins 0).nio_5Freq_5Fbits_5Fdw = 1 := by
      have h := legal.2
      bv_decide
  · simpa [total, specification, op, full] using
      (MulDivMultiply.signed_high_result s pins idle valid (Or.inl op) full
        (by simpa [total, full] using resets) (by simpa [total, full] using kills)).2.1
  · simpa [total, specification, op, full] using
      (MulDivMultiply.signed_high_result s pins idle valid (Or.inr op) full
        (by simpa [total, full] using resets) (by simpa [total, full] using kills)).2.1
  · simpa [total, specification, op, full] using
      (MulDivMultiply.unsigned_high_result s pins idle valid op full
        (by simpa [total, full] using resets) (by simpa [total, full] using kills)).2.1

end MulDivCheckedMulSpec
