import Proofs.MulDivUnsigned

namespace MulDivSigned
open nMulDiv
open MulDivDivision (packed)
open MulDivOutput (metadata)

def operand (i : Inputs) (x : BitVec 64) : BitVec 64 :=
  if i.nio_5Freq_5Fbits_5Fdw = 1 then x else (x.extractLsb' 0 32).signExtend 64

def magnitude (x : BitVec 64) : BitVec 64 := if x.msb then -x else x

def needsNegation (i : Inputs) : Bool :=
  (operand i i.nio_5Freq_5Fbits_5Fin1).msb || (operand i i.nio_5Freq_5Fbits_5Fin2).msb

def outputNegative (i : Inputs) : BitVec 1 :=
  BitVec.ofBool (if i.nio_5Freq_5Fbits_5Ffn = 6 then (operand i i.nio_5Freq_5Fbits_5Fin1).msb
    else (operand i i.nio_5Freq_5Fbits_5Fin1).msb != (operand i i.nio_5Freq_5Fbits_5Fin2).msb)

def prepared (s : State) (i later : Inputs) : State :=
  if needsNegation i then step (step s i) later else step s i

/-- Actual capture and optional neg_inputs edge produce unsigned magnitudes,
including the minimum signed input, with word sign extension done first. -/
theorem preparation (s : State) (i later : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Freq_5Fvalid = 1)
    (reset : i.nreset = 0) (laterReset : later.nreset = 0) (laterKill : later.nio_5Fkill = 0)
    (operation : i.nio_5Freq_5Fbits_5Ffn = 4 ∨ i.nio_5Freq_5Fbits_5Ffn = 6) :
    (prepared s i later).r0_nstate = 3 ∧ (prepared s i later).r3_ncount = 0 ∧
    (prepared s i later).r7_ndivisor = 0#1 ++ magnitude (operand i i.nio_5Freq_5Fbits_5Fin2) ∧
    packed (prepared s i later) = 0#65 ++ magnitude (operand i i.nio_5Freq_5Fbits_5Fin1) ∧
    (prepared s i later).r4_nneg_5Fout = outputNegative i ∧
    metadata (prepared s i later) = (i.nio_5Freq_5Fbits_5Fdw, i.nio_5Freq_5Fbits_5Ftag,
      if i.nio_5Freq_5Fbits_5Ffn = 6 then 1 else 0) := by
  rcases operation with operation | operation <;>
    simp only [prepared, needsNegation, operand, magnitude, outputNegative,
      packed, metadata, step, eval, idle, valid, reset, laterReset, laterKill,
      operation, Prod.mk.injEq] <;> bv_decide

end MulDivSigned
