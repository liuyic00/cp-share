import Proofs.MulDivCheckedDivisionChecks

namespace MulDivCheckedData
open nMulDivChecked
open MulDivCheckedDivisionChecks (quotient residue)

def format (s : State) (value : BitVec 64) : BitVec 64 :=
  if s.r12_ncontractDw = 1 then value else
    BitVec.replicate 32 (value.extractLsb' 31 1) ++ value.extractLsb' 0 32

def divisionValue (s : State) : BitVec 64 :=
  let selected := if s.r11_ncontractFn.extractLsb' 1 1 = 1 then residue s else quotient s
  if MulDivCheckedLatency.outputNegative s = 1 then 0 - selected else selected

def product (s : State) : BitVec 128 :=
  let signedA : BitVec 1 := (if s.r11_ncontractFn = 1 then 1 else 0) ||| (if s.r11_ncontractFn = 2 then 1 else 0)
  let signedB : BitVec 1 := if s.r11_ncontractFn = 1 then 1 else 0
  (BitVec.replicate 64 (signedA &&& s.r13_ncontractA.extractLsb' 63 1) ++ s.r13_ncontractA) *
    (BitVec.replicate 64 (signedB &&& s.r14_ncontractB.extractLsb' 63 1) ++ s.r14_ncontractB)

/-- Keep the exported one-bit comparison guard so `data_check` is definitional. -/
def multiplyValue (s : State) : BitVec 64 :=
  if (if s.r11_ncontractFn = 0 then (1 : BitVec 1) else 0) = 1 then (product s).extractLsb' 0 64 else (product s).extractLsb' 64 64

def expected (s : State) : BitVec 64 := format s
  (if s.r11_ncontractFn.extractLsb' 2 1 = 1 then divisionValue s else multiplyValue s)

def gate (s : State) (i : Inputs) : BitVec 1 :=
  ((s.r9_ncontractPending &&& (i.nio_5Fkill ^^^ 1)) &&& (observe s i).nio_5Fresp_5Fvalid) &&& (i.nreset ^^^ 1)

theorem data_check (s : State) (i : Inputs) : (eval s i).assertions[3]! =
    decide (gate s i ≠ 1 ∨ (if (observe s i).nio_5Fresp_5Fbits_5Fdata = expected s then (1 : BitVec 1) else 0) = 1) := by
  rfl

theorem inactive (s : State) (i : Inputs)
    (disabled : ¬ (s.r9_ncontractPending = 1 ∧ (observe s i).nio_5Fresp_5Fvalid = 1)) :
    (eval s i).assertions[3]! = true := by
  have zero : gate s i = 0 := by simp only [gate]; bv_decide
  rw [data_check]
  simp [zero]

theorem of_correct (s : State) (i : Inputs)
    (correct : (observe s i).nio_5Fresp_5Fbits_5Fdata = expected s) :
    (eval s i).assertions[3]! = true := by
  rw [data_check]
  simp [correct]

end MulDivCheckedData
