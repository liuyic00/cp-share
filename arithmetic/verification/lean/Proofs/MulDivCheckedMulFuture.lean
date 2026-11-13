import Proofs.MulDivCheckedMulSpec

namespace MulDivCheckedMulFuture
open nMulDivChecked
open MulDivCheckedMulSpec (specification)

def Computing (s : State) : Prop := ∀ pins : Nat → nMulDiv.Inputs,
  (∀ t, t < 64 - s.r3_ncount.toNat → (pins t).nreset = 0) →
  (∀ t, t < 64 - s.r3_ncount.toNat → (pins t).nio_5Fkill = 0) →
  (nMulDiv.observe (nMulDiv.run (MulDivCheckedProjection.state s) pins (64 - s.r3_ncount.toNat))
    (pins (64 - s.r3_ncount.toNat))).nio_5Fresp_5Fbits_5Fdata = specification (MulDivCheckedHistory.captured s)

theorem capture_computing (s : State) (i : Inputs) (idle : s.r0_nstate = 0)
    (valid : i.nio_5Freq_5Fvalid = 1) (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0)
    (legal : MulDivCheckedMulSpec.Legal (MulDivCheckedProjection.inputs i)) : Computing (step s i) := by
  have count : (step s i).r3_ncount = (if i.nio_5Freq_5Fbits_5Fdw = 1 then 0 else 32) := by
    have range := legal.1
    simp only [MulDivCheckedProjection.inputs] at range
    simp only [step, eval, idle, valid]
    bv_decide
  have total : MulDivCheckedMulSpec.total (MulDivCheckedProjection.inputs i) =
      (64 - (step s i).r3_ncount.toNat) + 1 := by
    rw [count]
    unfold MulDivCheckedMulSpec.total MulDivCheckedProjection.inputs
    split <;> decide
  intro pins resets kills
  let extended : Nat → nMulDiv.Inputs := fun t => match t with
    | 0 => MulDivCheckedProjection.inputs i
    | n + 1 => pins n
  have allResets : ∀ t, t < MulDivCheckedMulSpec.total (extended 0) → (extended t).nreset = 0 := by
    intro t bound
    change t < MulDivCheckedMulSpec.total (MulDivCheckedProjection.inputs i) at bound
    rw [total] at bound
    cases t with
    | zero => exact reset
    | succ t => exact resets t (by omega)
  have allKills : ∀ t, t < MulDivCheckedMulSpec.total (extended 0) → (extended t).nio_5Fkill = 0 := by
    intro t bound
    change t < MulDivCheckedMulSpec.total (MulDivCheckedProjection.inputs i) at bound
    rw [total] at bound
    cases t with
    | zero => exact kill
    | succ t => exact kills t (by omega)
  have result := MulDivCheckedMulSpec.accepted_result (MulDivCheckedProjection.state s) extended
    idle valid legal allResets allKills
  change (nMulDiv.observe (nMulDiv.run _ extended (MulDivCheckedMulSpec.total (MulDivCheckedProjection.inputs i)))
    (extended (MulDivCheckedMulSpec.total (MulDivCheckedProjection.inputs i)))).nio_5Fresp_5Fbits_5Fdata = _ at result
  rw [total, MulDivControl.run_from_next] at result
  change _ = specification (MulDivCheckedHistory.captured (step s i))
  rw [MulDivCheckedHistory.capture s i idle valid]
  exact result

theorem computing_step (s : State) (i : Inputs) (state : s.r0_nstate = 2)
    (count : s.r3_ncount.toNat < 63) (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0)
    (computing : Computing s) : Computing (step s i) := by
  have edge := MulDivControl.mul_edge (MulDivCheckedProjection.state s)
    (MulDivCheckedProjection.inputs i) state reset kill
  have nextCount : (step s i).r3_ncount.toNat = s.r3_ncount.toNat + 1 := by
    have h := congrArg BitVec.toNat edge.2
    change (step s i).r3_ncount.toNat = (s.r3_ncount + 1).toNat at h
    rw [h, BitVec.toNat_add]
    change (s.r3_ncount.toNat + 1) % 128 = _
    omega
  have remaining : 64 - s.r3_ncount.toNat = (64 - (step s i).r3_ncount.toNat) + 1 := by omega
  have stable := MulDivCheckedHistory.hold s i (Or.inl (by rw [state]; decide))
  intro pins resets kills
  let extended : Nat → nMulDiv.Inputs := fun t => match t with
    | 0 => MulDivCheckedProjection.inputs i
    | n + 1 => pins n
  have allResets : ∀ t, t < 64 - s.r3_ncount.toNat → (extended t).nreset = 0 := by
    intro t bound
    cases t with
    | zero => exact reset
    | succ t => exact resets t (by omega)
  have allKills : ∀ t, t < 64 - s.r3_ncount.toNat → (extended t).nio_5Fkill = 0 := by
    intro t bound
    cases t with
    | zero => exact kill
    | succ t => exact kills t (by omega)
  have result := computing extended allResets allKills
  rw [remaining, MulDivControl.run_from_next] at result
  change _ = specification (MulDivCheckedHistory.captured (step s i))
  rw [stable]
  exact result

theorem computing_last (s : State) (i later : Inputs) (state : s.r0_nstate = 2)
    (count : s.r3_ncount = 63) (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0)
    (computing : Computing s) : (observe (step s i) later).nio_5Fresp_5Fbits_5Fdata =
      specification (MulDivCheckedHistory.captured (step s i)) := by
  let pins : Nat → nMulDiv.Inputs := fun t => if t = 0 then MulDivCheckedProjection.inputs i
    else MulDivCheckedProjection.inputs later
  have remaining : 64 - s.r3_ncount.toNat = 1 := by rw [count]; decide
  have resets : ∀ t, t < 64 - s.r3_ncount.toNat → (pins t).nreset = 0 := by
    intro t bound
    rw [remaining] at bound
    have zero : t = 0 := by omega
    simpa [pins, zero] using reset
  have kills : ∀ t, t < 64 - s.r3_ncount.toNat → (pins t).nio_5Fkill = 0 := by
    intro t bound
    rw [remaining] at bound
    have zero : t = 0 := by omega
    simpa [pins, zero] using kill
  have result := computing pins resets kills
  rw [remaining] at result
  rw [MulDivCheckedHistory.hold s i (Or.inl (by rw [state]; decide))]
  exact result

end MulDivCheckedMulFuture
