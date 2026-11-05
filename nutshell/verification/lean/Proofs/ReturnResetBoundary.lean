import Proofs.ReturnTrainingAlignment
namespace NutShellProofs
open nNutCore

/-- A local two-transition witness against unconditional all-slot alignment.
This does not assert a counterexample to the original environment/contract. -/
theorem reset_stale_call_writes_unaligned_slot (s : State) (i j : Inputs)
    (reset : i.g0.nreset = 1) (released : j.g0.nreset = 0)
    (valid : v6 s i = 1) (unit : v3 s i = 0) (flush : v23 s i = 0)
    (operation : v28 s i = 92)
    (pc : s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc = 2)
    (width : BitVec.extractLsb' 0 2 (v11547 s i) = 3) :
    (step (step s i) j).g32.r1038_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F1 = 6 ∧
    (step (step s i) j).g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = 1 := by
  have train := return_training_valid_without_reset_gate s i j valid unit flush operation
  have call : v8208 (step s i) j = 1 := by
    change (if v12141 s i = BitVec.ofNat 7 92 then (1 : BitVec 1) else 0) = 1
    simp [v12141, operation]
  have stackPointer : (step s i).g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = 0 := by
    change v8335 s i = 0
    simp [v8335, v2, v1, v0, reset, v8317]
  have trainingPC : v73 (step s i) j = 2 := by
    change v12145 s i = 2
    exact pc
  have trainingWidth : v104 (step s i) j = 0 := by
    change v12193 s i = 0
    simp [v12193, v12192, v12191, width, v2750]
  constructor
  · change v8233 (step s i) j = 6
    simp [v8233, v2, v1, v0, released, v8232, train, v8231, call,
      v8230, v8229, v8228, v8213, v8212, v8210, v8211, v24, stackPointer,
      v8223, trainingWidth, v8222, v8221, v8219, v8220, trainingPC]
  · change v8335 (step s i) j = 1
    simp [v8335, v2, v1, v0, released, v8334, train, v8333, call,
      v8321, v8320, v8318, v8319, v24, stackPointer]

/-- The pointer produced by the stale call selects the poisoned slot directly. -/
theorem return_read_slot_one (s : State) (i : Inputs)
    (ptr : s.g32.r1053_nfrontend_5Fifu_5Fbp1_5Fsp_5Fvalue = 1)
    (slot : s.g32.r1038_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F1 = 6) :
    v8376 s i = 6 := by
  simp [v8376, v8336, v15, v8375, v8337, v8306, v8374, v8338, v8300, v8373, v8339, v8294, v8372, v8340, v8288, v8371, v8341, v8282, v8370, v8342, v8276, v8369, v8343, v8270, v8368, v8345, v8344, v8367, v8347, v8346, v8366, v8349, v8348, v8365, v8351, v8350, v8364, v8353, v8352, v8363, v8355, v8354, v8362, v8357, v8356, ptr, slot]

#print axioms return_read_slot_one
#print axioms reset_stale_call_writes_unaligned_slot
end NutShellProofs
