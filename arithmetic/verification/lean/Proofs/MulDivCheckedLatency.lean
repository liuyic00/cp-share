import Proofs.MulDivCheckedHistory
import Proofs.MulDivSignedOutput

namespace MulDivCheckedLatency
set_option maxHeartbeats 2000000
open nMulDivChecked

def signedBit (s : State) : BitVec 1 := s.r11_ncontractFn.extractLsb' 0 1 ^^^ 1

def operand (s : State) (x : BitVec 64) : BitVec 64 :=
  if s.r12_ncontractDw = 1 then x else
    BitVec.replicate 32 (signedBit s &&& x.extractLsb' 31 1) ++ x.extractLsb' 0 32

def negative (s : State) (x : BitVec 64) : BitVec 1 :=
  signedBit s &&& (operand s x).extractLsb' 63 1

def magnitude (s : State) (x : BitVec 64) : BitVec 64 :=
  if negative s x = 1 then 0 - operand s x else operand s x

def outputNegative (s : State) : BitVec 1 :=
  if s.r11_ncontractFn.extractLsb' 1 1 = 1 then negative s s.r13_ncontractA else
    (if negative s s.r13_ncontractA ≠ negative s s.r14_ncontractB then 1 else 0) &&&
      (if magnitude s s.r14_ncontractB ≠ 0 then 1 else 0)

/-- The exact bit-vector expression used by the two exported timing checks. -/
def latency (s : State) : BitVec 7 :=
  if s.r11_ncontractFn.extractLsb' 2 1 = 1 then
    ((0#6 ++ (negative s s.r13_ncontractA ||| negative s s.r14_ncontractB)) +
      (0#6 ++ outputNegative s)) + 65
  else if s.r12_ncontractDw = 1 then 64 else 32

def gate (s : State) (i : Inputs) : BitVec 1 :=
  (s.r9_ncontractPending &&& (i.nio_5Fkill ^^^ 1)) &&& (i.nreset ^^^ 1)

theorem timing_checks (s : State) (i : Inputs) :
    (eval s i).assertions.take 2 =
      [decide (gate s i ≠ 1 ∨ (if s.r10_ncontractAge.toNat ≤ (latency s).toNat then (1 : BitVec 1) else 0) = 1),
       decide (gate s i ≠ 1 ∨ (if (observe s i).nio_5Fresp_5Fvalid =
         (if s.r10_ncontractAge = latency s then (1 : BitVec 1) else 0) then (1 : BitVec 1) else 0) = 1)] := by
  rfl

theorem signed_latency_bits (s : State)
    (operation : s.r11_ncontractFn = 4 ∨ s.r11_ncontractFn = 6) :
    latency s = ((0#6 ++ BitVec.ofBool (MulDivSigned.needsNegation (MulDivCheckedHistory.captured s))) +
      (0#6 ++ MulDivSigned.effectiveNegative
        (MulDivSigned.magnitude (MulDivSigned.operand (MulDivCheckedHistory.captured s) s.r14_ncontractB))
        (if s.r11_ncontractFn = 6 then 1 else 0)
        (MulDivSigned.outputNegative (MulDivCheckedHistory.captured s)))) + 65 := by
  rcases operation with operation | operation <;>
    simp only [latency, negative, operand, magnitude, signedBit, outputNegative,
      MulDivCheckedHistory.captured, MulDivSigned.needsNegation, MulDivSigned.operand,
      MulDivSigned.magnitude, MulDivSigned.outputNegative, MulDivSigned.effectiveNegative, operation] <;>
    bv_decide

private theorem cycle_arithmetic (b : Bool) (negative : BitVec 1) :
    (((0#6 ++ BitVec.ofBool b) + (0#6 ++ negative)) + 65).toNat + 1 =
      (if b then 2 else 1) + 65 + (if negative = 1 then 1 else 0) := by
  have cases : negative = 0 ∨ negative = 1 := by bv_decide
  rcases cases with h | h <;> subst negative <;> cases b <;> decide

/-- The source monitor's further-edge count agrees with the exact signed
DIV/REM theorem, including word inputs and division by zero. -/
theorem signed_exact_cycle (s : State)
    (operation : s.r11_ncontractFn = 4 ∨ s.r11_ncontractFn = 6) :
    (latency s).toNat + 1 = MulDivSigned.acceptedEdges (MulDivCheckedHistory.captured s) := by
  rw [signed_latency_bits s operation, cycle_arithmetic]
  rfl

theorem capture_cycle (s : State) (i : Inputs) (ready : s.r0_nstate = 0)
    (valid : i.nio_5Freq_5Fvalid = 1)
    (operation : i.nio_5Freq_5Fbits_5Ffn = 4 ∨ i.nio_5Freq_5Fbits_5Ffn = 6) :
    (latency (step s i)).toNat + 1 = MulDivSigned.acceptedEdges (MulDivCheckedProjection.inputs i) := by
  have capture := MulDivCheckedHistory.capture s i ready valid
  have fn := congrArg nMulDiv.Inputs.nio_5Freq_5Fbits_5Ffn capture
  change (step s i).r11_ncontractFn = i.nio_5Freq_5Fbits_5Ffn at fn
  have capturedOperation : (step s i).r11_ncontractFn = 4 ∨ (step s i).r11_ncontractFn = 6 := by
    rw [fn]
    exact operation
  rw [signed_exact_cycle _ capturedOperation, capture]
  rfl

/-- Signed division on the instrumented circuit produces the correct result
at exactly the cycle specified by its captured source monitor. Later request
pins are arbitrary; reset and cancellation are excluded during this request. -/
theorem signed_result_at_monitor_cycle (s : State) (pins : Nat → Inputs)
    (ready : s.r0_nstate = 0) (valid : (pins 0).nio_5Freq_5Fvalid = 1)
    (operation : (pins 0).nio_5Freq_5Fbits_5Ffn = 4 ∨ (pins 0).nio_5Freq_5Fbits_5Ffn = 6)
    (resets : ∀ t, t < 68 → (pins t).nreset = 0)
    (kills : ∀ t, t < 68 → (pins t).nio_5Fkill = 0) :
    let n := (latency (step s (pins 0))).toNat + 1
    (observe (run s pins n) (pins n)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s pins n) (pins n)).nio_5Fresp_5Fbits_5Fdata =
      MulDivSigned.specification (MulDivCheckedProjection.inputs (pins 0)) ∧
    (observe (run s pins n) (pins n)).nio_5Fresp_5Fbits_5Ftag = (pins 0).nio_5Freq_5Fbits_5Ftag := by
  obtain ⟨n, cycle, _, _, response⟩ := MulDivSigned.accepted_result_exact
    (MulDivCheckedProjection.state s) (fun t => MulDivCheckedProjection.inputs (pins t))
    ready valid operation resets kills
  have monitor := capture_cycle s (pins 0) ready valid operation
  have equal : n = (latency (step s (pins 0))).toNat + 1 := cycle.trans monitor.symm
  rw [equal] at response
  rw [← MulDivCheckedProjection.run_projects, ← MulDivCheckedProjection.observe_projects] at response
  exact response

end MulDivCheckedLatency
