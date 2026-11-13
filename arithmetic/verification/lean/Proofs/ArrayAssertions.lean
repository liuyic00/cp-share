import Proofs.ArrayProduct
import Proofs.ArrayStall
import Proofs.ArrayCompressors

namespace ArrayAssertions
open nArrayMulDataModule
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem and_left (x y : BitVec 1) (h : x &&& y = 1) : x = 1 := by bv_decide

theorem product_check (s : State) (i : Inputs) (invariant : ArrayProduct.ResultInvariant s) :
    v59795 s i ≠ 1 ∨ v59793 s i = 1 := by
  by_cases enabled : v59795 s i = 1
  · right
    have known : s.g79.r2537_nresultKnown = 1 := and_left _ _ enabled
    have correct := invariant i known
    change v16460 s i = s.g79.r2536_nexpectedResult at correct
    simp only [v59793, correct, if_true]
  · exact Or.inl enabled

theorem all_checks (s : State) (i : Inputs)
    (product : v59795 s i ≠ 1 ∨ v59793 s i = 1)
    (stall : v59797 s i ≠ 1 ∨ v59796 s i = 1) :
    (assertionChecks s i).all id = true := by
  simp [assertionChecks, ArrayCompressors.chunk_0, ArrayCompressors.chunk_1, ArrayCompressors.chunk_2, ArrayCompressors.chunk_3, ArrayCompressors.chunk_4, ArrayCompressors.chunk_5, ArrayCompressors.chunk_6, ArrayCompressors.chunk_7, ArrayCompressors.chunk_8, ArrayCompressors.chunk_9, ArrayCompressors.chunk_10, ArrayCompressors.chunk_11, ArrayCompressors.chunk_12, ArrayCompressors.chunk_13, ArrayCompressors.chunk_14, ArrayCompressors.chunk_15, ArrayCompressors.chunk_16, ArrayCompressors.chunk_17, ArrayCompressors.chunk_18, ArrayCompressors.chunk_19, ArrayCompressors.chunk_20, ArrayCompressors.chunk_21, ArrayCompressors.chunk_22, ArrayCompressors.chunk_23, ArrayCompressors.chunk_24, ArrayCompressors.chunk_25, ArrayCompressors.chunk_26, ArrayCompressors.chunk_27, ArrayCompressors.chunk_28, ArrayCompressors.chunk_29, ArrayCompressors.chunk_30, ArrayCompressors.chunk_31, ArrayCompressors.chunk_32, ArrayCompressors.chunk_33, ArrayCompressors.chunk_34, ArrayCompressors.chunk_35, ArrayCompressors.chunk_36, ArrayCompressors.chunk_37, ArrayCompressors.chunk_38, ArrayCompressors.chunk_39, ArrayCompressors.chunk_40, ArrayCompressors.chunk_41, ArrayCompressors.chunk_42, ArrayCompressors.chunk_43, ArrayCompressors.chunk_44, ArrayCompressors.chunk_45, ArrayCompressors.chunk_46, ArrayCompressors.chunk_47, ArrayCompressors.chunk_48, ArrayCompressors.chunk_49, ArrayCompressors.chunk_50, ArrayCompressors.chunk_51, ArrayCompressors.chunk_52, ArrayCompressors.chunk_53, ArrayCompressors.chunk_54, ArrayCompressors.chunk_55, ArrayCompressors.chunk_56, ArrayCompressors.chunk_57, ArrayCompressors.chunk_58, ArrayCompressors.chunk_59, ArrayCompressors.chunk_60, ArrayCompressors.chunk_61, ArrayCompressors.chunk_62, ArrayCompressors.chunk_63, ArrayCompressors.chunk_64, ArrayCompressors.chunk_65, ArrayCompressors.chunk_66, ArrayCompressors.chunk_67, ArrayCompressors.chunk_68, ArrayCompressors.chunk_69, ArrayCompressors.chunk_70, ArrayCompressors.chunk_71, ArrayCompressors.chunk_72, ArrayCompressors.chunk_73, ArrayCompressors.chunk_74, ArrayCompressors.chunk_75, ArrayCompressors.chunk_76, ArrayCompressors.chunk_77, ArrayCompressors.chunk_78, ArrayCompressors.chunk_79, ArrayCompressors.chunk_80, ArrayCompressors.chunk_81, ArrayCompressors.chunk_82, ArrayCompressors.chunk_83, ArrayCompressors.chunk_84, ArrayCompressors.chunk_85, ArrayCompressors.chunk_86, ArrayCompressors.chunk_87, ArrayCompressors.chunk_88, ArrayCompressors.chunk_89, ArrayCompressors.chunk_90, ArrayCompressors.chunk_91, ArrayCompressors.chunk_92, ArrayCompressors.chunk_93, ArrayCompressors.chunk_94, ArrayCompressors.chunk_95, ArrayCompressors.chunk_96, ArrayCompressors.chunk_97, ArrayCompressors.chunk_98, ArrayCompressors.chunk_99, ArrayCompressors.chunk_100, ArrayCompressors.chunk_101, ArrayCompressors.chunk_102, ArrayCompressors.chunk_103, ArrayCompressors.chunk_104, ArrayCompressors.chunk_105, ArrayCompressors.chunk_106, ArrayCompressors.chunk_107, ArrayCompressors.chunk_108]
  exact ⟨product, stall⟩

/-- Every exported local, product, and hold assertion holds on every cycle
after reset, with arbitrary subsequent operand pins, enables, and resets. -/
theorem all_assertions_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    (assertionChecks (run (step s resetInput) inputs n) (inputs n)).all id = true := by
  have invariant := ArrayProduct.invariant_after_reset s resetInput reset inputs n
  have product := product_check _ (inputs n) invariant.2.2
  cases n with
  | zero => exact all_checks _ _ product (ArrayStall.stall_check s resetInput (inputs 0))
  | succ n =>
    exact all_checks _ _ product
      (ArrayStall.stall_check (run (step s resetInput) inputs n) (inputs n) (inputs (n+1)))

end ArrayAssertions
