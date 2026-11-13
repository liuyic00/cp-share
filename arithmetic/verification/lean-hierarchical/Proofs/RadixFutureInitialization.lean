import Proofs.RadixFuture
import Proofs.RadixZeroContract

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

private theorem unshift (a : BitVec 64) : BitVec.extractLsb' 1 64 (a ++ 0#1) = a := by
  bv_decide

theorem initialized_future (s : State) (accept setup load : Inputs)
    (idle : s.r0_nstate = 0) (valid : accept.nio_5Fin_5Fvalid = 1)
    (r0 : accept.nreset = 0) (r1 : setup.nreset = 0) (r2 : load.nreset = 0) :
    FutureResult (step (step (step s accept) setup) load) := by
  let captured := step s accept
  let loaded := step (step captured setup) load
  have capture := capture_request s accept idle valid r0
  have fields := initialized_fields captured setup load capture.1 r1 r2
  have setupState := setup_control captured setup capture.1 r1
  have payload1 := arithmetic_payload_stable captured setup (by rw [capture.1]; decide)
  have payload2 := arithmetic_payload_stable (step captured setup) load (by rw [setupState]; decide)
  have flag : loaded.r1_ndivBy0Reg = captured.r1_ndivBy0Reg := payload2.2.2.trans payload1.2.2
  have divisor : loaded.r5_nbReg = magnitude accept.nio_5Fin_5Fbits_5Fsrc_5F1 accept.nctrl_5Fsign :=
    fields.2.1.trans capture.2.1
  have dividend : loaded.r6_naValx2Reg = magnitude accept.nio_5Fin_5Fbits_5Fsrc_5F0 accept.nctrl_5Fsign ++ 0#1 :=
    fields.2.2.1.trans capture.2.2.1
  change FutureResult loaded
  unfold FutureResult ResultWords
  rw [flag]
  by_cases zero : accept.nio_5Fin_5Fbits_5Fsrc_5F1 = 0#64
  · have flagSet := capture_zero_flag s accept idle valid zero
    have zeroFields := initialized_zero s accept setup load idle valid r0 r1 r2 zero
    change captured.r1_ndivBy0Reg = 1#1 at flagSet
    rw [flagSet]
    constructor
    · intro _
      change _ = _ ∧ _ = _
      rw [show loaded.r5_nbReg = 0#64 from zeroFields.2.1,
        show loaded.r9_ncnt_5Fvalue = 0#6 from zeroFields.2.2.1,
        show loaded.r2_nshiftReg = _ from zeroFields.2.2.2, dividend, unshift]
      exact zero_result _
    · intro impossible
      contradiction
  · have flagClear := capture_nonzero s accept idle valid zero
    change captured.r1_ndivBy0Reg = 0#1 at flagClear
    rw [flagClear]
    constructor
    · intro impossible
      contradiction
    · intro _
      have arithmetic := initialized_arithmetic s accept setup load idle valid r0 r1 r2 zero
      change (BitVec.extractLsb' 0 64 (advanceMany loaded.r5_nbReg
        (64 - loaded.r9_ncnt_5Fvalue.toNat) loaded.r2_nshiftReg)).toNat = _ ∧
        (BitVec.extractLsb' 65 64 (advanceMany loaded.r5_nbReg
        (64 - loaded.r9_ncnt_5Fvalue.toNat) loaded.r2_nshiftReg)).toNat = _ at arithmetic
      rw [arithmetic.1, arithmetic.2, divisor, dividend, unshift]
      have nonzero := magnitude_nonzero accept.nio_5Fin_5Fbits_5Fsrc_5F1 accept.nctrl_5Fsign zero
      have positive : 0 < (magnitude accept.nio_5Fin_5Fbits_5Fsrc_5F1 accept.nctrl_5Fsign).toNat := by
        have h : (magnitude accept.nio_5Fin_5Fbits_5Fsrc_5F1 accept.nctrl_5Fsign).toNat ≠ 0 := by
          intro eq
          apply nonzero
          apply BitVec.eq_of_toNat_eq
          exact eq
        omega
      constructor
      · rw [Nat.mul_comm]
        exact Nat.div_add_mod _ _
      · exact Nat.mod_lt _ positive

end HierarchicalRadix
