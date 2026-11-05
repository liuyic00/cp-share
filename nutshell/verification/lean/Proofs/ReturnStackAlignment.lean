import Proofs.FetchSequentialAlignment
namespace NutShellProofs
open nNutCore
def ReturnStackAligned (s : State) : Prop :=
  BitVec.extractLsb' 0 2 s.g32.r1037_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F0 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1038_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F1 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1039_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F2 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1040_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F3 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1041_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F4 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1042_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F5 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1043_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F6 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1044_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F7 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1045_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F8 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1046_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F9 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1047_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F10 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1048_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F11 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1049_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F12 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1050_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F13 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1051_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F14 = 0 ∧
  BitVec.extractLsb' 0 2 s.g32.r1052_nfrontend_5Fifu_5Fbp1_5Fregs_5F1_5F15 = 0
theorem return_stack_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    ReturnStackAligned (step s i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change BitVec.extractLsb' 0 2 (v8227 s i) = 0
    simp [v8227, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8233 s i) = 0
    simp [v8233, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8239 s i) = 0
    simp [v8239, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8245 s i) = 0
    simp [v8245, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8251 s i) = 0
    simp [v8251, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8257 s i) = 0
    simp [v8257, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8263 s i) = 0
    simp [v8263, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8269 s i) = 0
    simp [v8269, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8275 s i) = 0
    simp [v8275, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8281 s i) = 0
    simp [v8281, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8287 s i) = 0
    simp [v8287, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8293 s i) = 0
    simp [v8293, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8299 s i) = 0
    simp [v8299, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8305 s i) = 0
    simp [v8305, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8311 s i) = 0
    simp [v8311, v2, v1, v0, reset, v8200]
  · change BitVec.extractLsb' 0 2 (v8316 s i) = 0
    simp [v8316, v2, v1, v0, reset, v8200]
theorem return_stack_step (s : State) (i : Inputs) (old : ReturnStackAligned s)
    (push : v63 s i = 1 → v8208 s i = 1 → BitVec.extractLsb' 0 2 (v8223 s i) = 0) :
    ReturnStackAligned (step s i) := by
  rcases old with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change BitVec.extractLsb' 0 2 (v8227 s i) = 0
    unfold v8227 v8226 v8225 v8224
    repeat' split
    all_goals first | exact h0 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8233 s i) = 0
    unfold v8233 v8232 v8231 v8230
    repeat' split
    all_goals first | exact h1 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8239 s i) = 0
    unfold v8239 v8238 v8237 v8236
    repeat' split
    all_goals first | exact h2 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8245 s i) = 0
    unfold v8245 v8244 v8243 v8242
    repeat' split
    all_goals first | exact h3 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8251 s i) = 0
    unfold v8251 v8250 v8249 v8248
    repeat' split
    all_goals first | exact h4 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8257 s i) = 0
    unfold v8257 v8256 v8255 v8254
    repeat' split
    all_goals first | exact h5 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8263 s i) = 0
    unfold v8263 v8262 v8261 v8260
    repeat' split
    all_goals first | exact h6 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8269 s i) = 0
    unfold v8269 v8268 v8267 v8266
    repeat' split
    all_goals first | exact h7 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8275 s i) = 0
    unfold v8275 v8274 v8273 v8272
    repeat' split
    all_goals first | exact h8 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8281 s i) = 0
    unfold v8281 v8280 v8279 v8278
    repeat' split
    all_goals first | exact h9 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8287 s i) = 0
    unfold v8287 v8286 v8285 v8284
    repeat' split
    all_goals first | exact h10 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8293 s i) = 0
    unfold v8293 v8292 v8291 v8290
    repeat' split
    all_goals first | exact h11 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8299 s i) = 0
    unfold v8299 v8298 v8297 v8296
    repeat' split
    all_goals first | exact h12 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8305 s i) = 0
    unfold v8305 v8304 v8303 v8302
    repeat' split
    all_goals first | exact h13 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8311 s i) = 0
    unfold v8311 v8310 v8309 v8308
    repeat' split
    all_goals first | exact h14 | exact push (by assumption) (by assumption) | rfl
  · change BitVec.extractLsb' 0 2 (v8316 s i) = 0
    unfold v8316 v8315 v8314 v8313
    repeat' split
    all_goals first | exact h15 | exact push (by assumption) (by assumption) | rfl
theorem return_stack_push_aligned (s : State) (i : Inputs)
    (pc : BitVec.extractLsb' 0 2 (v73 s i) = 0)
    (fullWidth : v104 s i = 0) : BitVec.extractLsb' 0 2 (v8223 s i) = 0 := by
  simp [v8223, fullWidth, v8222, v8221, v8219, v8220, v24,
    low_low _ (by decide : 2 ≤ 39), low_add _ _ (by decide : 2 ≤ 40),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 39), pc]
#print axioms return_stack_push_aligned
#print axioms return_stack_reset
#print axioms return_stack_step
end NutShellProofs
