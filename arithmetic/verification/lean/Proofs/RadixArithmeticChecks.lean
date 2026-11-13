import Proofs.RadixTemporal
import Proofs.RadixResult

namespace nRadix2Divider
set_option maxRecDepth 8192

/-- The widened exported multiply/add check expresses an integer identity. -/
theorem widened_division_identity (q b r a : BitVec 64)
    (identity : q.toNat * b.toNat + r.toNat = a.toNat) :
    (0#1 ++ ((0#64 ++ q) * (0#64 ++ b))) + (0#65 ++ r) = (0#65 ++ a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_append,
    BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  have bound := a.isLt
  have productBound : q.toNat * b.toNat < 2^128 := by omega
  rw [Nat.mod_eq_of_lt productBound, identity, Nat.mod_eq_of_lt (by omega)]

/-- A completed nonzero division with the mathematical quotient and remainder
satisfies all five arithmetic assertions emitted from Chisel. -/
theorem arithmetic_checks_nonzero (s : State) (i : Inputs)
    (flag : s.r1_ndivBy0Reg = 0) (nonzero : s.r5_nbReg.toNat > 0)
    (quotient : (s.r2_nshiftReg.extractLsb' 0 64).toNat =
      (s.r6_naValx2Reg.extractLsb' 1 64).toNat / s.r5_nbReg.toNat)
    (remainder : (s.r2_nshiftReg.extractLsb' 65 64).toNat =
      (s.r6_naValx2Reg.extractLsb' 1 64).toNat % s.r5_nbReg.toNat) :
    ((eval s i).assertions.take 5).all id = true := by
  have identity := widened_division_identity (s.r2_nshiftReg.extractLsb' 0 64) s.r5_nbReg
    (s.r2_nshiftReg.extractLsb' 65 64) (s.r6_naValx2Reg.extractLsb' 1 64) (by
      rw [quotient, remainder, Nat.mul_comm, Nat.div_add_mod])
  have small : (s.r2_nshiftReg.extractLsb' 65 64).toNat < s.r5_nbReg.toNat := by
    rw [remainder]
    exact Nat.mod_lt _ nonzero
  have divisor : s.r5_nbReg ≠ 0 := by intro h; rw [h] at nonzero; contradiction
  simp only [eval, List.take, List.all_cons, List.all_nil, id_eq, flag, identity, small]
  bv_decide

theorem arithmetic_checks_zero (s : State) (i : Inputs)
    (flag : s.r1_ndivBy0Reg = 1)
    (quotient : s.r2_nshiftReg.extractLsb' 0 64 = 18446744073709551615)
    (remainder : s.r2_nshiftReg.extractLsb' 65 64 = s.r6_naValx2Reg.extractLsb' 1 64) :
    ((eval s i).assertions.take 5).all id = true := by
  simp only [eval, List.take, List.all_cons, List.all_nil, id_eq, flag, quotient, remainder]
  bv_decide

theorem arithmetic_checks_inactive (s : State) (i : Inputs)
    (inactive : s.r0_nstate ≠ 4 ∨ i.nreset = 1) :
    ((eval s i).assertions.take 5).all id = true := by
  simp only [eval, List.take, List.all_cons, List.all_nil, id_eq]
  bv_decide

theorem asserts_reset_edge (s : State) (resetInput i : Inputs)
    (reset : resetInput.nreset = 1) : asserts (step s resetInput) i := by
  rw [asserts_after_edge_iff]
  apply arithmetic_checks_inactive
  left
  rw [reset_idle s resetInput reset]
  decide

theorem asserts_nonzero_after_edge (s : State) (previous i : Inputs)
    (flag : (step s previous).r1_ndivBy0Reg = 0)
    (nonzero : (step s previous).r5_nbReg.toNat > 0)
    (quotient : ((step s previous).r2_nshiftReg.extractLsb' 0 64).toNat =
      ((step s previous).r6_naValx2Reg.extractLsb' 1 64).toNat / (step s previous).r5_nbReg.toNat)
    (remainder : ((step s previous).r2_nshiftReg.extractLsb' 65 64).toNat =
      ((step s previous).r6_naValx2Reg.extractLsb' 1 64).toNat % (step s previous).r5_nbReg.toNat) :
    asserts (step s previous) i := by
  rw [asserts_after_edge_iff]
  exact arithmetic_checks_nonzero _ i flag nonzero quotient remainder

theorem asserts_zero_after_edge (s : State) (previous i : Inputs)
    (flag : (step s previous).r1_ndivBy0Reg = 1)
    (quotient : (step s previous).r2_nshiftReg.extractLsb' 0 64 = 18446744073709551615)
    (remainder : (step s previous).r2_nshiftReg.extractLsb' 65 64 =
      (step s previous).r6_naValx2Reg.extractLsb' 1 64) :
    asserts (step s previous) i := by
  rw [asserts_after_edge_iff]
  exact arithmetic_checks_zero _ i flag quotient remainder

end nRadix2Divider
