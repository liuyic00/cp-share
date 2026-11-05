import Proofs.ReferenceBitFacts
import Proofs.RegisterExecution
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
def refExec_v4 (a b : BitVec 32) : BitVec 1 := BitVec.ofNat 1 0
def refExec_v2300 (a b : BitVec 32) : BitVec 33 := ((refExec_v4 a b) ++ a)
def refExec_v2301 (a b : BitVec 32) : BitVec 33 := ((refExec_v4 a b) ++ b)
def refExec_v2302 (a b : BitVec 32) : BitVec 33 := ((refExec_v2300 a b) + (refExec_v2301 a b))
def refExec_v2303 (a b : BitVec 32) : BitVec 32 := BitVec.extractLsb' 0 32 (refExec_v2302 a b)
def refExec_v2263 (a b : BitVec 32) : BitVec 33 := ((refExec_v4 a b) ++ a)
def refExec_v2264 (a b : BitVec 32) : BitVec 33 := ((refExec_v4 a b) ++ b)
def refExec_v2265 (a b : BitVec 32) : BitVec 33 := ((refExec_v2263 a b) - (refExec_v2264 a b))
def refExec_v2266 (a b : BitVec 32) : BitVec 32 := BitVec.extractLsb' 0 32 (refExec_v2265 a b)
def refExec_v2289 (a b : BitVec 32) : BitVec 32 := (a &&& b)
def refExec_v2286 (a b : BitVec 32) : BitVec 32 := (a ||| b)
def refExec_v2283 (a b : BitVec 32) : BitVec 32 := (a ^^^ b)
def refExec_v2274 (a b : BitVec 32) : BitVec 31 := BitVec.ofNat 31 0
def refExec_v2296 (a b : BitVec 32) : BitVec 1 := if a.toInt < b.toInt then 1 else 0
def refExec_v2297 (a b : BitVec 32) : BitVec 32 := ((refExec_v2274 a b) ++ (refExec_v2296 a b))
def refExec_v2275 (a b : BitVec 32) : BitVec 63 := ((refExec_v2274 a b) ++ a)
def refExec_v2276 (a b : BitVec 32) : BitVec 58 := BitVec.ofNat 58 0
def refExec_v2277 (a b : BitVec 32) : BitVec 5 := BitVec.extractLsb' 0 5 b
def refExec_v2278 (a b : BitVec 32) : BitVec 63 := ((refExec_v2276 a b) ++ (refExec_v2277 a b))
def refExec_v2279 (a b : BitVec 32) : BitVec 63 := BitVec.shiftLeft (refExec_v2275 a b) (refExec_v2278 a b).toNat
def refExec_v2280 (a b : BitVec 32) : BitVec 32 := BitVec.extractLsb' 0 32 (refExec_v2279 a b)
def refExec_v2292 (a b : BitVec 32) : BitVec 1 := if a.toNat < b.toNat then 1 else 0
def refExec_v2293 (a b : BitVec 32) : BitVec 32 := ((refExec_v2274 a b) ++ (refExec_v2292 a b))
def refExec_v2104 (a b : BitVec 32) : BitVec 27 := BitVec.ofNat 27 0
def refExec_v2269 (a b : BitVec 32) : BitVec 5 := BitVec.extractLsb' 0 5 b
def refExec_v2270 (a b : BitVec 32) : BitVec 32 := ((refExec_v2104 a b) ++ (refExec_v2269 a b))
def refExec_v2271 (a b : BitVec 32) : BitVec 32 := BitVec.ushiftRight a (refExec_v2270 a b).toNat
def refExec_v2258 (a b : BitVec 32) : BitVec 5 := BitVec.extractLsb' 0 5 b
def refExec_v2259 (a b : BitVec 32) : BitVec 32 := ((refExec_v2104 a b) ++ (refExec_v2258 a b))
def refExec_v2260 (a b : BitVec 32) : BitVec 32 := BitVec.sshiftRight a (refExec_v2259 a b).toNat
theorem reference_add_cone (s : State) (i : Inputs) :
    v2303 s i = refExec_v2303 (v1721 s i) (v1539 s i) := by rfl
theorem reference_execution_add (a b : BitVec 32) :
    refExec_v2303 a b = aluSpec 0 a b := by
  simp only [refExec_v2260, refExec_v2259, refExec_v2258, refExec_v2271, refExec_v2270, refExec_v2269, refExec_v2104, refExec_v2293, refExec_v2292, refExec_v2280, refExec_v2279, refExec_v2278, refExec_v2277, refExec_v2276, refExec_v2275, refExec_v2297, refExec_v2296, refExec_v2274, refExec_v2283, refExec_v2286, refExec_v2289, refExec_v2266, refExec_v2265, refExec_v2264, refExec_v2263, refExec_v2303, refExec_v2302, refExec_v2301, refExec_v2300, refExec_v4]
  simp [aluSpec, ref_zero_append_nat (n := 27) (w := 5),
    ref_zero_append_nat (n := 58) (w := 5)]
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_sub,
    ref_zero_append_nat (n := 1) (w := 32)]
#print axioms reference_execution_add
theorem decoded_reference_arithmetic_add (s : State) (i : Inputs)
    (instruction pc : BitVec 32)
    (known : instruction &&& 4261441663 = 51) :
    decodedExecution instruction pc (v1721 s i) (v1539 s i) = v2303 s i := by
  rw [reference_add_cone, reference_execution_add]
  exact decoded_execution_add _ _ _ _ known
#print axioms decoded_reference_arithmetic_add
theorem reference_sub_cone (s : State) (i : Inputs) :
    v2266 s i = refExec_v2266 (v1721 s i) (v1539 s i) := by rfl
theorem reference_execution_sub (a b : BitVec 32) :
    refExec_v2266 a b = aluSpec 1 a b := by
  simp only [refExec_v2260, refExec_v2259, refExec_v2258, refExec_v2271, refExec_v2270, refExec_v2269, refExec_v2104, refExec_v2293, refExec_v2292, refExec_v2280, refExec_v2279, refExec_v2278, refExec_v2277, refExec_v2276, refExec_v2275, refExec_v2297, refExec_v2296, refExec_v2274, refExec_v2283, refExec_v2286, refExec_v2289, refExec_v2266, refExec_v2265, refExec_v2264, refExec_v2263, refExec_v2303, refExec_v2302, refExec_v2301, refExec_v2300, refExec_v4]
  simp [aluSpec, ref_zero_append_nat (n := 27) (w := 5),
    ref_zero_append_nat (n := 58) (w := 5)]
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_sub,
    ref_zero_append_nat (n := 1) (w := 32)]
  omega
#print axioms reference_execution_sub
theorem decoded_reference_arithmetic_sub (s : State) (i : Inputs)
    (instruction pc : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) :
    decodedExecution instruction pc (v1721 s i) (v1539 s i) = v2266 s i := by
  rw [reference_sub_cone, reference_execution_sub]
  exact decoded_execution_sub _ _ _ _ known
#print axioms decoded_reference_arithmetic_sub
theorem reference_and_cone (s : State) (i : Inputs) :
    v2289 s i = refExec_v2289 (v1721 s i) (v1539 s i) := by rfl
theorem reference_execution_and (a b : BitVec 32) :
    refExec_v2289 a b = aluSpec 2 a b := by
  simp only [refExec_v2260, refExec_v2259, refExec_v2258, refExec_v2271, refExec_v2270, refExec_v2269, refExec_v2104, refExec_v2293, refExec_v2292, refExec_v2280, refExec_v2279, refExec_v2278, refExec_v2277, refExec_v2276, refExec_v2275, refExec_v2297, refExec_v2296, refExec_v2274, refExec_v2283, refExec_v2286, refExec_v2289, refExec_v2266, refExec_v2265, refExec_v2264, refExec_v2263, refExec_v2303, refExec_v2302, refExec_v2301, refExec_v2300, refExec_v4]
  simp [aluSpec, ref_zero_append_nat (n := 27) (w := 5),
    ref_zero_append_nat (n := 58) (w := 5)]
#print axioms reference_execution_and
theorem decoded_reference_arithmetic_and (s : State) (i : Inputs)
    (instruction pc : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) :
    decodedExecution instruction pc (v1721 s i) (v1539 s i) = v2289 s i := by
  rw [reference_and_cone, reference_execution_and]
  exact decoded_execution_and _ _ _ _ known
#print axioms decoded_reference_arithmetic_and
theorem reference_or_cone (s : State) (i : Inputs) :
    v2286 s i = refExec_v2286 (v1721 s i) (v1539 s i) := by rfl
theorem reference_execution_or (a b : BitVec 32) :
    refExec_v2286 a b = aluSpec 3 a b := by
  simp only [refExec_v2260, refExec_v2259, refExec_v2258, refExec_v2271, refExec_v2270, refExec_v2269, refExec_v2104, refExec_v2293, refExec_v2292, refExec_v2280, refExec_v2279, refExec_v2278, refExec_v2277, refExec_v2276, refExec_v2275, refExec_v2297, refExec_v2296, refExec_v2274, refExec_v2283, refExec_v2286, refExec_v2289, refExec_v2266, refExec_v2265, refExec_v2264, refExec_v2263, refExec_v2303, refExec_v2302, refExec_v2301, refExec_v2300, refExec_v4]
  simp [aluSpec, ref_zero_append_nat (n := 27) (w := 5),
    ref_zero_append_nat (n := 58) (w := 5)]
#print axioms reference_execution_or
theorem decoded_reference_arithmetic_or (s : State) (i : Inputs)
    (instruction pc : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) :
    decodedExecution instruction pc (v1721 s i) (v1539 s i) = v2286 s i := by
  rw [reference_or_cone, reference_execution_or]
  exact decoded_execution_or _ _ _ _ known
#print axioms decoded_reference_arithmetic_or
theorem reference_xor_cone (s : State) (i : Inputs) :
    v2283 s i = refExec_v2283 (v1721 s i) (v1539 s i) := by rfl
theorem reference_execution_xor (a b : BitVec 32) :
    refExec_v2283 a b = aluSpec 4 a b := by
  simp only [refExec_v2260, refExec_v2259, refExec_v2258, refExec_v2271, refExec_v2270, refExec_v2269, refExec_v2104, refExec_v2293, refExec_v2292, refExec_v2280, refExec_v2279, refExec_v2278, refExec_v2277, refExec_v2276, refExec_v2275, refExec_v2297, refExec_v2296, refExec_v2274, refExec_v2283, refExec_v2286, refExec_v2289, refExec_v2266, refExec_v2265, refExec_v2264, refExec_v2263, refExec_v2303, refExec_v2302, refExec_v2301, refExec_v2300, refExec_v4]
  simp [aluSpec, ref_zero_append_nat (n := 27) (w := 5),
    ref_zero_append_nat (n := 58) (w := 5)]
#print axioms reference_execution_xor
theorem decoded_reference_arithmetic_xor (s : State) (i : Inputs)
    (instruction pc : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) :
    decodedExecution instruction pc (v1721 s i) (v1539 s i) = v2283 s i := by
  rw [reference_xor_cone, reference_execution_xor]
  exact decoded_execution_xor _ _ _ _ known
#print axioms decoded_reference_arithmetic_xor
theorem reference_slt_cone (s : State) (i : Inputs) :
    v2297 s i = refExec_v2297 (v1721 s i) (v1539 s i) := by rfl
theorem reference_execution_slt (a b : BitVec 32) :
    refExec_v2297 a b = aluSpec 5 a b := by
  simp only [refExec_v2260, refExec_v2259, refExec_v2258, refExec_v2271, refExec_v2270, refExec_v2269, refExec_v2104, refExec_v2293, refExec_v2292, refExec_v2280, refExec_v2279, refExec_v2278, refExec_v2277, refExec_v2276, refExec_v2275, refExec_v2297, refExec_v2296, refExec_v2274, refExec_v2283, refExec_v2286, refExec_v2289, refExec_v2266, refExec_v2265, refExec_v2264, refExec_v2263, refExec_v2303, refExec_v2302, refExec_v2301, refExec_v2300, refExec_v4]
  simp [aluSpec, ref_zero_append_nat (n := 27) (w := 5),
    ref_zero_append_nat (n := 58) (w := 5)]
  split <;> rfl
#print axioms reference_execution_slt
theorem decoded_reference_arithmetic_slt (s : State) (i : Inputs)
    (instruction pc : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) :
    decodedExecution instruction pc (v1721 s i) (v1539 s i) = v2297 s i := by
  rw [reference_slt_cone, reference_execution_slt]
  exact decoded_execution_slt _ _ _ _ known
#print axioms decoded_reference_arithmetic_slt
theorem reference_sll_cone (s : State) (i : Inputs) :
    v2280 s i = refExec_v2280 (v1721 s i) (v1539 s i) := by rfl
theorem reference_execution_sll (a b : BitVec 32) :
    refExec_v2280 a b = aluSpec 6 a b := by
  simp only [refExec_v2260, refExec_v2259, refExec_v2258, refExec_v2271, refExec_v2270, refExec_v2269, refExec_v2104, refExec_v2293, refExec_v2292, refExec_v2280, refExec_v2279, refExec_v2278, refExec_v2277, refExec_v2276, refExec_v2275, refExec_v2297, refExec_v2296, refExec_v2274, refExec_v2283, refExec_v2286, refExec_v2289, refExec_v2266, refExec_v2265, refExec_v2264, refExec_v2263, refExec_v2303, refExec_v2302, refExec_v2301, refExec_v2300, refExec_v4]
  simp [aluSpec, ref_zero_append_nat (n := 27) (w := 5),
    ref_zero_append_nat (n := 58) (w := 5)]
  exact ref_zero_extend_shift_left a _
#print axioms reference_execution_sll
theorem decoded_reference_arithmetic_sll (s : State) (i : Inputs)
    (instruction pc : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) :
    decodedExecution instruction pc (v1721 s i) (v1539 s i) = v2280 s i := by
  rw [reference_sll_cone, reference_execution_sll]
  exact decoded_execution_sll _ _ _ _ known
#print axioms decoded_reference_arithmetic_sll
theorem reference_sltu_cone (s : State) (i : Inputs) :
    v2293 s i = refExec_v2293 (v1721 s i) (v1539 s i) := by rfl
theorem reference_execution_sltu (a b : BitVec 32) :
    refExec_v2293 a b = aluSpec 7 a b := by
  simp only [refExec_v2260, refExec_v2259, refExec_v2258, refExec_v2271, refExec_v2270, refExec_v2269, refExec_v2104, refExec_v2293, refExec_v2292, refExec_v2280, refExec_v2279, refExec_v2278, refExec_v2277, refExec_v2276, refExec_v2275, refExec_v2297, refExec_v2296, refExec_v2274, refExec_v2283, refExec_v2286, refExec_v2289, refExec_v2266, refExec_v2265, refExec_v2264, refExec_v2263, refExec_v2303, refExec_v2302, refExec_v2301, refExec_v2300, refExec_v4]
  simp [aluSpec, ref_zero_append_nat (n := 27) (w := 5),
    ref_zero_append_nat (n := 58) (w := 5)]
  split <;> rfl
#print axioms reference_execution_sltu
theorem decoded_reference_arithmetic_sltu (s : State) (i : Inputs)
    (instruction pc : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) :
    decodedExecution instruction pc (v1721 s i) (v1539 s i) = v2293 s i := by
  rw [reference_sltu_cone, reference_execution_sltu]
  exact decoded_execution_sltu _ _ _ _ known
#print axioms decoded_reference_arithmetic_sltu
theorem reference_srl_cone (s : State) (i : Inputs) :
    v2271 s i = refExec_v2271 (v1721 s i) (v1539 s i) := by rfl
theorem reference_execution_srl (a b : BitVec 32) :
    refExec_v2271 a b = aluSpec 8 a b := by
  simp only [refExec_v2260, refExec_v2259, refExec_v2258, refExec_v2271, refExec_v2270, refExec_v2269, refExec_v2104, refExec_v2293, refExec_v2292, refExec_v2280, refExec_v2279, refExec_v2278, refExec_v2277, refExec_v2276, refExec_v2275, refExec_v2297, refExec_v2296, refExec_v2274, refExec_v2283, refExec_v2286, refExec_v2289, refExec_v2266, refExec_v2265, refExec_v2264, refExec_v2263, refExec_v2303, refExec_v2302, refExec_v2301, refExec_v2300, refExec_v4]
  simp [aluSpec, ref_zero_append_nat (n := 27) (w := 5),
    ref_zero_append_nat (n := 58) (w := 5)]
#print axioms reference_execution_srl
theorem decoded_reference_arithmetic_srl (s : State) (i : Inputs)
    (instruction pc : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) :
    decodedExecution instruction pc (v1721 s i) (v1539 s i) = v2271 s i := by
  rw [reference_srl_cone, reference_execution_srl]
  exact decoded_execution_srl _ _ _ _ known
#print axioms decoded_reference_arithmetic_srl
theorem reference_sra_cone (s : State) (i : Inputs) :
    v2260 s i = refExec_v2260 (v1721 s i) (v1539 s i) := by rfl
theorem reference_execution_sra (a b : BitVec 32) :
    refExec_v2260 a b = aluSpec 9 a b := by
  simp only [refExec_v2260, refExec_v2259, refExec_v2258, refExec_v2271, refExec_v2270, refExec_v2269, refExec_v2104, refExec_v2293, refExec_v2292, refExec_v2280, refExec_v2279, refExec_v2278, refExec_v2277, refExec_v2276, refExec_v2275, refExec_v2297, refExec_v2296, refExec_v2274, refExec_v2283, refExec_v2286, refExec_v2289, refExec_v2266, refExec_v2265, refExec_v2264, refExec_v2263, refExec_v2303, refExec_v2302, refExec_v2301, refExec_v2300, refExec_v4]
  simp [aluSpec, ref_zero_append_nat (n := 27) (w := 5),
    ref_zero_append_nat (n := 58) (w := 5)]
#print axioms reference_execution_sra
theorem decoded_reference_arithmetic_sra (s : State) (i : Inputs)
    (instruction pc : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) :
    decodedExecution instruction pc (v1721 s i) (v1539 s i) = v2260 s i := by
  rw [reference_sra_cone, reference_execution_sra]
  exact decoded_execution_sra _ _ _ _ known
#print axioms decoded_reference_arithmetic_sra
end RiscvMiniProofs
