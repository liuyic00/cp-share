import Proofs.MulDivCheckedDivisionInit

namespace MulDivCheckedMagnitude
open nMulDivChecked
open MulDivCheckedLatency (magnitude)

def parameters (s : State) : BitVec 64 × BitVec 64 :=
  (magnitude s s.r13_ncontractA, magnitude s s.r14_ncontractB)

def Correct (s : nMulDiv.State) (a d : BitVec 64) : Prop :=
  (MulDivDivision.packed s).extractLsb' 0 64 =
    (if d = 0 then BitVec.allOnes 64 else BitVec.ofNat 64 (a.toNat / d.toNat)) ∧
  (MulDivDivision.packed s).extractLsb' 65 64 = BitVec.ofNat 64 (a.toNat % d.toNat)

/-- The remaining actual restoring iterations compute the magnitudes of the
captured operands, regardless of the later request pins and response readiness. -/
def Computing (s : State) : Prop := ∀ pins : Nat → nMulDiv.Inputs,
  (∀ t, t < 65 - s.r3_ncount.toNat → (pins t).nreset = 0) →
  (∀ t, t < 65 - s.r3_ncount.toNat → (pins t).nio_5Fkill = 0) →
  Correct (nMulDiv.run (MulDivCheckedProjection.state s) pins (65 - s.r3_ncount.toNat))
    (parameters s).1 (parameters s).2

theorem parameters_hold (s : State) (i : Inputs) (busy : s.r0_nstate ≠ 0) :
    parameters (step s i) = parameters s := by
  change s.r0_nstate ≠ 0#3 at busy
  simp [parameters, magnitude, MulDivCheckedLatency.negative, MulDivCheckedLatency.operand,
    MulDivCheckedLatency.signedBit, step, eval, busy]

theorem initialized_computing (s : State) (state : s.r0_nstate = 3) (count : s.r3_ncount = 0)
    (initialized : MulDivCheckedDivisionInit.Initialized s) : Computing s := by
  have packed : MulDivDivision.packed (MulDivCheckedProjection.state s) =
      0#65 ++ (parameters s).1 := by
    change s.r8_nremainder.extractLsb' 0 129 = _
    rw [initialized.1]
    simp only [parameters]
    bv_decide
  intro pins resets kills
  have result := MulDivUnsigned.magnitudes (MulDivCheckedProjection.state s) pins
    (parameters s).1 (parameters s).2 state count initialized.2 packed
    (by simpa [count] using resets) (by simpa [count] using kills)
  simpa only [Correct, count, BitVec.toNat_ofNat, Nat.sub_zero] using result

theorem computing_step (s : State) (i : Inputs) (state : s.r0_nstate = 3)
    (count : s.r3_ncount.toNat < 64) (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0)
    (computing : Computing s) : Computing (step s i) := by
  have edge := MulDivControl.div_edge (MulDivCheckedProjection.state s)
    (MulDivCheckedProjection.inputs i) state reset kill
  have nextCount : (step s i).r3_ncount.toNat = s.r3_ncount.toNat + 1 := by
    have h := congrArg BitVec.toNat edge.2
    change (step s i).r3_ncount.toNat = (s.r3_ncount + 1).toNat at h
    rw [h, BitVec.toNat_add]
    change (s.r3_ncount.toNat + 1) % 128 = _
    omega
  have remaining : 65 - s.r3_ncount.toNat = (65 - (step s i).r3_ncount.toNat) + 1 := by omega
  have stable := parameters_hold s i (by rw [state]; decide)
  intro pins resets kills
  let extended : Nat → nMulDiv.Inputs := fun t => match t with
    | 0 => MulDivCheckedProjection.inputs i
    | n + 1 => pins n
  have allResets : ∀ t, t < 65 - s.r3_ncount.toNat → (extended t).nreset = 0 := by
    intro t bound
    cases t with
    | zero => exact reset
    | succ t => exact resets t (by omega)
  have allKills : ∀ t, t < 65 - s.r3_ncount.toNat → (extended t).nio_5Fkill = 0 := by
    intro t bound
    cases t with
    | zero => exact kill
    | succ t => exact kills t (by omega)
  have result := computing extended allResets allKills
  rw [remaining, MulDivControl.run_from_next] at result
  change Correct (nMulDiv.run (MulDivCheckedProjection.state (step s i)) pins
    (65 - (step s i).r3_ncount.toNat)) (parameters (step s i)).1 (parameters (step s i)).2
  rw [stable, MulDivCheckedProjection.step_projects]
  exact result

theorem computing_last (s : State) (i : Inputs) (state : s.r0_nstate = 3) (count : s.r3_ncount = 64)
    (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0) (computing : Computing s) :
    Correct (MulDivCheckedProjection.state (step s i)) (parameters (step s i)).1 (parameters (step s i)).2 := by
  have result := computing (fun _ => MulDivCheckedProjection.inputs i) (fun _ _ => reset) (fun _ _ => kill)
  have remaining : 65 - s.r3_ncount.toNat = 1 := by rw [count]; decide
  rw [remaining] at result
  have busy : s.r0_nstate ≠ 0 := by rw [state]; decide
  rw [parameters_hold s i busy]
  exact result

end MulDivCheckedMagnitude
