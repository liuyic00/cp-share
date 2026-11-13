import Proofs.RadixAssertions
import Proofs.RadixExecution

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

def ResultWords (bits : BitVec 129) (divisor : BitVec 64)
    (dividend : BitVec 65) (zeroFlag : BitVec 1) : Prop :=
  (zeroFlag = 1 → BitVec.extractLsb' 0 64 bits = BitVec.allOnes 64 ∧
    BitVec.extractLsb' 65 64 bits = BitVec.extractLsb' 1 64 dividend) ∧
  (zeroFlag = 0 →
    (BitVec.extractLsb' 0 64 bits).toNat * divisor.toNat +
      (BitVec.extractLsb' 65 64 bits).toNat = (BitVec.extractLsb' 1 64 dividend).toNat ∧
    (BitVec.extractLsb' 65 64 bits).toNat < divisor.toNat)

def FutureResult (s : State) : Prop :=
  ResultWords (advanceMany s.r5_nbReg (64 - s.r9_ncnt_5Fvalue.toNat) s.r2_nshiftReg)
    s.r5_nbReg s.r6_naValx2Reg s.r1_ndivBy0Reg

theorem advanceMany_next (b : BitVec 64) (n : Nat) (bits : BitVec 129) :
    advanceMany b n (advance bits b) = advanceMany b (n + 1) bits := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [advanceMany] at ih ⊢; rw [ih]

theorem arithmetic_payload_stable (s : State) (i : Inputs) (active : s.r0_nstate ≠ 0#3) :
    (step s i).r5_nbReg = s.r5_nbReg ∧
    (step s i).r6_naValx2Reg = s.r6_naValx2Reg ∧
    (step s i).r1_ndivBy0Reg = s.r1_ndivBy0Reg := by
  simp [step, eval_eq_spec, evalSpec, v0, v1, v2, v55, v59, v24, active]

theorem future_compute (s : State) (i : Inputs) (computing : s.r0_nstate = 3)
    (reset : i.nreset = 0) (notLast : s.r9_ncnt_5Fvalue ≠ 63#6)
    (future : FutureResult s) : FutureResult (step s i) := by
  have control := computing_control s i computing reset
  have payload := arithmetic_payload_stable s i (by rw [computing]; decide)
  have count : (s.r9_ncnt_5Fvalue + 1#6).toNat = s.r9_ncnt_5Fvalue.toNat + 1 := by
    have bound := s.r9_ncnt_5Fvalue.isLt
    have different : s.r9_ncnt_5Fvalue.toNat ≠ 63 := by
      intro h
      apply notLast
      apply BitVec.eq_of_toNat_eq
      exact h
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  unfold FutureResult at future ⊢
  rw [payload.1, payload.2.1, payload.2.2, compute_edge s i computing, control.2, count,
    advanceMany_next]
  have bound := s.r9_ncnt_5Fvalue.isLt
  have remaining : 64 - (s.r9_ncnt_5Fvalue.toNat + 1) + 1 = 64 - s.r9_ncnt_5Fvalue.toNat := by omega
  rw [remaining]
  exact future

theorem future_finishes (s : State) (i : Inputs) (computing : s.r0_nstate = 3)
    (last : s.r9_ncnt_5Fvalue = 63#6) (future : FutureResult s) :
    ResultInvariant (step s i) := by
  intro _
  have payload := arithmetic_payload_stable s i (by rw [computing]; decide)
  change ResultWords (step s i).r2_nshiftReg (step s i).r5_nbReg
    (step s i).r6_naValx2Reg (step s i).r1_ndivBy0Reg
  rw [payload.1, payload.2.1, payload.2.2, compute_edge s i computing]
  unfold FutureResult at future
  rw [last] at future
  exact future

end HierarchicalRadix
