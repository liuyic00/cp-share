import Proofs.MulDivSignedProduct
import Proofs.MulDivUnsignedProduct

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

def productBits (a : BitVec 64) (d : BitVec 65) (negative : BitVec 1) : BitVec 128 :=
  BitVec.ofInt 128 (((a.toNat : Int) - (if negative = 1#1 then 2 ^ 64 else 0)) * d.toInt)

theorem product_state (s : State) (inputs : Nat → Inputs) (a : BitVec 64) (d : BitVec 65)
    (multiplying : s.r0_nstate = 2) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = d) (initial : s.r8_nremainder = 0#66 ++ a)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    (run s inputs 64).r0_nstate = 6 ∧
    (unpackMultiply (run s inputs 64).r8_nremainder).setWidth 128 = productBits a d s.r4_nneg_5Fout ∧
    metadata (run s inputs 64) = metadata s := by
  have finish := multiplication_finishes s inputs multiplying 0
    (by rw [count]; rfl) (by omega) reset alive
  refine ⟨finish.1, ?_, finish.2.2⟩
  rw [finish.2.1, divisor, initial]
  exact signed_packed_product a d s.r4_nneg_5Fout

theorem high_product_core_result (s : State) (inputs : Nat → Inputs) (a : BitVec 64) (d : BitVec 65)
    (multiplying : s.r0_nstate = 2) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = d) (initial : s.r8_nremainder = 0#66 ++ a)
    (full : s.r1_nreq_5Fdw = 1) (high : s.r5_nisHi = 1)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 64) (inputs 64)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 64) (inputs 64)).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
    (observe (run s inputs 64) (inputs 64)).nio_5Fresp_5Fbits_5Fdata =
      BitVec.extractLsb' 64 64 (productBits a d s.r4_nneg_5Fout) := by
  have result := product_state s inputs a d multiplying count divisor initial reset alive
  have before := multiplication_prefix s inputs multiplying 0 (by rw [count]; rfl) reset alive 63 (by omega)
  have counter : (run s inputs 63).r3_ncount = 63#7 := BitVec.eq_of_toNat_eq before.2.1
  have previousMetadata := metadata_run s inputs 63 (by
    intro t bound
    have traceFacts := multiplication_prefix s inputs multiplying 0 (by rw [count]; rfl) reset alive t (by omega)
    rw [traceFacts.1]
    decide)
  have mode : (run s inputs 64).r6_nresHi = 1 :=
    (select_multiply_response _ _ before.1 counter).trans
      ((congrArg (fun m => m.2.2) previousMetadata).trans high)
  have width : (run s inputs 64).r1_nreq_5Fdw = 1 :=
    (congrArg (fun m => m.1) result.2.2).trans full
  have output := observe_high_product (run s inputs 64) (inputs 64) result.1 width mode
  refine ⟨output.1, output.2.1.trans (congrArg (fun m => m.2.1) result.2.2), ?_⟩
  rw [output.2.2]
  have slice : BitVec.extractLsb' 65 64 (run s inputs 64).r8_nremainder =
      BitVec.extractLsb' 64 64 ((unpackMultiply (run s inputs 64).r8_nremainder).setWidth 128) := by
    unfold unpackMultiply
    bv_decide
  rw [slice, result.2.1]

def highProductSpecification (i : Inputs) : BitVec 64 :=
  BitVec.extractLsb' 64 64 (productBits i.nio_5Freq_5Fbits_5Fin1
    ((if i.nio_5Freq_5Fbits_5Ffn = 1#4 then operandSign i.nio_5Freq_5Fbits_5Fin2 else 0#1) ++ i.nio_5Freq_5Fbits_5Fin2)
    (if i.nio_5Freq_5Fbits_5Ffn = 3#4 then 0#1 else operandSign i.nio_5Freq_5Fbits_5Fin1))

/-- All three high-product instructions reuse the same computation contract
    and return the captured request's product after 65 edges. -/
theorem high_product_accepted (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 1#4 ∨
      (inputs 0).nio_5Freq_5Fbits_5Ffn = 2#4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 3#4)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Fdata = highProductSpecification (inputs 0) := by
  have captured := capture_high_product s (inputs 0) idle valid (reset 0 (by omega)) full operation
  have output := high_product_core_result (step s (inputs 0)) (fun t => inputs (1 + t)) _ _
    captured.1 captured.2.1 captured.2.2.1 captured.2.2.2.1
    (congrArg (fun m => m.1) captured.2.2.2.2.2.2)
    (congrArg (fun m => m.2.2) captured.2.2.2.2.2.2)
    (by intro t h; exact reset (1 + t) (by omega))
    (by intro t h; exact alive (1 + t) (by omega))
  have trajectory := run_offset s inputs 1 64
  change run s inputs 65 = run (step s (inputs 0)) (fun t => inputs (1 + t)) 64 at trajectory
  rw [trajectory]
  refine ⟨output.1, output.2.1.trans (congrArg (fun m => m.2.1) captured.2.2.2.2.2.2), ?_⟩
  rw [output.2.2, captured.2.2.2.2.1]
  rfl

#print axioms high_product_accepted
#print axioms high_product_core_result
end HierarchicalMulDiv
