import Proofs.MulDivCheckedMulSpec

namespace MulDivCheckedProductBits

/-- The source monitor's 128-bit product retains exactly the high half used by
an independently specified signed product at width 129. -/
theorem signed_high (a b : BitVec 64) :
    (BitVec.ofInt 129 (a.toInt * b.toInt)).extractLsb' 64 64 =
    ((BitVec.replicate 64 (a.extractLsb' 63 1) ++ a) *
      (BitVec.replicate 64 (b.extractLsb' 63 1) ++ b)).extractLsb' 64 64 := by
  have narrow (x : BitVec 129) : x.extractLsb' 64 64 = (x.setWidth 128).extractLsb' 64 64 := by bv_decide
  have extend (x : BitVec 64) : (BitVec.ofInt 129 x.toInt).setWidth 128 =
      BitVec.replicate 64 (x.extractLsb' 63 1) ++ x := by
    change (x.signExtend 129).setWidth 128 = _
    bv_decide
  rw [narrow, BitVec.ofInt_mul, BitVec.setWidth_mul _ _ (by decide), extend, extend]

theorem mixed_high (a b : BitVec 64) :
    (BitVec.ofInt 129 (a.toInt * (b.toNat : Int))).extractLsb' 64 64 =
    ((BitVec.replicate 64 (a.extractLsb' 63 1) ++ a) * (0#64 ++ b)).extractLsb' 64 64 := by
  have narrow (x : BitVec 129) : x.extractLsb' 64 64 = (x.setWidth 128).extractLsb' 64 64 := by bv_decide
  have extend : (BitVec.ofInt 129 a.toInt).setWidth 128 =
      BitVec.replicate 64 (a.extractLsb' 63 1) ++ a := by
    change (a.signExtend 129).setWidth 128 = _
    bv_decide
  have unsigned : (BitVec.ofInt 129 (b.toNat : Int)).setWidth 128 = 0#64 ++ b := by
    rw [BitVec.ofInt_natCast, BitVec.setWidth_ofNat_of_le (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_append, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
    exact Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))
  rw [narrow, BitVec.ofInt_mul, BitVec.setWidth_mul _ _ (by decide), extend, unsigned]

theorem unsigned_high (a b : BitVec 64) :
    BitVec.ofNat 64 ((a.toNat * b.toNat) / 18446744073709551616) =
      ((0#64 ++ a) * (0#64 ++ b)).extractLsb' 64 64 := by
  apply BitVec.eq_of_toNat_eq
  have bound := Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt
  change a.toNat * b.toNat < 2^128 at bound
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, BitVec.toNat_mul,
    BitVec.toNat_append, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  rw [Nat.mod_eq_of_lt bound, Nat.shiftRight_eq_div_pow]

theorem low (a b : BitVec 64) :
    a * b = ((0#64 ++ a) * (0#64 ++ b)).extractLsb' 0 64 := by
  rw [← BitVec.setWidth_eq_extractLsb' (by decide), BitVec.setWidth_mul _ _ (by decide)]
  have narrow (x : BitVec 64) : (0#64 ++ x).setWidth 64 = x := by bv_decide
  rw [narrow, narrow]

theorem word (a b : BitVec 64) :
    ((a.extractLsb' 0 32) * (b.extractLsb' 0 32)).signExtend 64 =
      (((0#64 ++ a) * (0#64 ++ b)).extractLsb' 0 32).signExtend 64 := by
  congr 1
  conv => rhs; rw [← BitVec.setWidth_eq_extractLsb' (by decide), BitVec.setWidth_mul _ _ (by decide)]
  have narrow (x : BitVec 64) : (0#64 ++ x).setWidth 32 = x.extractLsb' 0 32 := by bv_decide
  rw [narrow, narrow]

end MulDivCheckedProductBits
