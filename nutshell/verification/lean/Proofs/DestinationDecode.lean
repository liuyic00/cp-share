import Proofs.InstructionWidth
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def DestinationDecoded (bit : Nat) (instr : BitVec 64) (kind : BitVec 1) (addr : BitVec 5) : Prop :=
  kind = 1 → addr = BitVec.extractLsb' bit 5 instr


def QueueDestination1_0 (s : State) : Prop :=
  DestinationDecoded 7 s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g53.r1724_ndataBuffer_5F0_5Fctrl_5FrfWen s.g53.r1725_ndataBuffer_5F0_5Fctrl_5FrfDest

theorem queue_destination1_0_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueDestination1_0 (step s i) := by
  change DestinationDecoded 7 (v26233 s i) (v28910 s i) (v28933 s i)
  simp [DestinationDecoded, v26233, v28910, v28933, reset, v24, v4051, v15076]

theorem queue_destination1_0_step (s : State) (i : Inputs) (old : QueueDestination1_0 s) :
    QueueDestination1_0 (step s i) := by
  change DestinationDecoded 7 (v26233 s i) (v28910 s i) (v28933 s i)
  change DestinationDecoded 7 s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr s.g53.r1724_ndataBuffer_5F0_5Fctrl_5FrfWen s.g53.r1725_ndataBuffer_5F0_5Fctrl_5FrfDest at old
  unfold DestinationDecoded at *
  simp only [v26233, v4051, v26232, v26231, v26230, v26208, v26203, v26213, v26212, v26211, v26229, v26228, v26221, v26216, v26227, v26226, v26225, v26224, v28910, v24, v28909, v28908, v28907, v28893, v28892, v28897, v28896, v28895, v28894, v28906, v28905, v28899, v28898, v28904, v28903, v28902, v28901, v28900, v28933, v15076, v28932, v28931, v28930, v28912, v28911, v28918, v28917, v28916, v28915, v28913, v28617, v28914, v28929, v28928, v28920, v28919, v28927, v28926, v28925, v28924, v28923, v28921, v28810, v28922]
  repeat' first | (split <;> try simp_all only [↓reduceIte]) | (intro h; try simp_all) | assumption
  all_goals try simp_all
  all_goals decide

def QueueDestination1_1 (s : State) : Prop :=
  DestinationDecoded 7 s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g55.r1779_ndataBuffer_5F1_5Fctrl_5FrfWen s.g55.r1780_ndataBuffer_5F1_5Fctrl_5FrfDest

theorem queue_destination1_1_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueDestination1_1 (step s i) := by
  change DestinationDecoded 7 (v29247 s i) (v29697 s i) (v29707 s i)
  simp [DestinationDecoded, v29247, v29697, v29707, reset, v24, v4051, v15076]

theorem queue_destination1_1_step (s : State) (i : Inputs) (old : QueueDestination1_1 s) :
    QueueDestination1_1 (step s i) := by
  change DestinationDecoded 7 (v29247 s i) (v29697 s i) (v29707 s i)
  change DestinationDecoded 7 s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr s.g55.r1779_ndataBuffer_5F1_5Fctrl_5FrfWen s.g55.r1780_ndataBuffer_5F1_5Fctrl_5FrfDest at old
  unfold DestinationDecoded at *
  simp only [v29247, v4051, v29246, v29245, v29244, v29239, v29238, v26213, v26212, v26211, v29243, v29242, v29241, v29240, v26227, v26226, v26225, v26224, v29697, v24, v29696, v29695, v29694, v29689, v29688, v28897, v28896, v28895, v28894, v29693, v29692, v29691, v29690, v28904, v28903, v28902, v28901, v28900, v29707, v15076, v29706, v29705, v29704, v29699, v29698, v28918, v28917, v28916, v28915, v28913, v28617, v28914, v29703, v29702, v29701, v29700, v28927, v28926, v28925, v28924, v28923, v28921, v28810, v28922]
  repeat' first | (split <;> try simp_all only [↓reduceIte]) | (intro h; try simp_all) | assumption
  all_goals try simp_all
  all_goals decide

def QueueDestination1_2 (s : State) : Prop :=
  DestinationDecoded 7 s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g57.r1834_ndataBuffer_5F2_5Fctrl_5FrfWen s.g57.r1835_ndataBuffer_5F2_5Fctrl_5FrfDest

theorem queue_destination1_2_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueDestination1_2 (step s i) := by
  change DestinationDecoded 7 (v29795 s i) (v30155 s i) (v30163 s i)
  simp [DestinationDecoded, v29795, v30155, v30163, reset, v24, v4051, v15076]

theorem queue_destination1_2_step (s : State) (i : Inputs) (old : QueueDestination1_2 s) :
    QueueDestination1_2 (step s i) := by
  change DestinationDecoded 7 (v29795 s i) (v30155 s i) (v30163 s i)
  change DestinationDecoded 7 s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr s.g57.r1834_ndataBuffer_5F2_5Fctrl_5FrfWen s.g57.r1835_ndataBuffer_5F2_5Fctrl_5FrfDest at old
  unfold DestinationDecoded at *
  simp only [v29795, v4051, v29794, v29793, v29792, v29788, v9721, v26213, v26212, v26211, v29791, v29790, v29789, v26227, v26226, v26225, v26224, v30155, v24, v30154, v30153, v30152, v30148, v28897, v28896, v28895, v28894, v30151, v30150, v30149, v28904, v28903, v28902, v28901, v28900, v30163, v15076, v30162, v30161, v30160, v30156, v28918, v28917, v28916, v28915, v28913, v28617, v28914, v30159, v30158, v30157, v28927, v28926, v28925, v28924, v28923, v28921, v28810, v28922]
  repeat' first | (split <;> try simp_all only [↓reduceIte]) | (intro h; try simp_all) | assumption
  all_goals try simp_all
  all_goals decide

def QueueDestination1_3 (s : State) : Prop :=
  DestinationDecoded 7 s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g59.r1889_ndataBuffer_5F3_5Fctrl_5FrfWen s.g59.r1890_ndataBuffer_5F3_5Fctrl_5FrfDest

theorem queue_destination1_3_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueDestination1_3 (step s i) := by
  change DestinationDecoded 7 (v30235 s i) (v30595 s i) (v30603 s i)
  simp [DestinationDecoded, v30235, v30595, v30603, reset, v24, v4051, v15076]

theorem queue_destination1_3_step (s : State) (i : Inputs) (old : QueueDestination1_3 s) :
    QueueDestination1_3 (step s i) := by
  change DestinationDecoded 7 (v30235 s i) (v30595 s i) (v30603 s i)
  change DestinationDecoded 7 s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr s.g59.r1889_ndataBuffer_5F3_5Fctrl_5FrfWen s.g59.r1890_ndataBuffer_5F3_5Fctrl_5FrfDest at old
  unfold DestinationDecoded at *
  simp only [v30235, v4051, v30234, v30233, v30232, v30228, v2750, v26213, v26212, v26211, v30231, v30230, v30229, v26227, v26226, v26225, v26224, v30595, v24, v30594, v30593, v30592, v30588, v28897, v28896, v28895, v28894, v30591, v30590, v30589, v28904, v28903, v28902, v28901, v28900, v30603, v15076, v30602, v30601, v30600, v30596, v28918, v28917, v28916, v28915, v28913, v28617, v28914, v30599, v30598, v30597, v28927, v28926, v28925, v28924, v28923, v28921, v28810, v28922]
  repeat' first | (split <;> try simp_all only [↓reduceIte]) | (intro h; try simp_all) | assumption
  all_goals try simp_all
  all_goals decide

def QueueDestinations1Decoded (s : State) : Prop :=
  QueueDestination1_0 s ∧ QueueDestination1_1 s ∧ QueueDestination1_2 s ∧ QueueDestination1_3 s

theorem queue_selected_destination1 (s : State) (i : Inputs) (queue : QueueDestinations1Decoded s) :
    DestinationDecoded 7 (v24297 s i) (v24946 s i) (v24948 s i) := by
  rcases queue with ⟨h0, h1, h2, h3⟩
  have bound := s.g59.r1900_nringBufferTail.isLt
  have cases : s.g59.r1900_nringBufferTail.toNat = 0 ∨ s.g59.r1900_nringBufferTail.toNat = 1 ∨ s.g59.r1900_nringBufferTail.toNat = 2 ∨ s.g59.r1900_nringBufferTail.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : s.g59.r1900_nringBufferTail = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24946, v24945, v24944, v24943, v24933, v24942, v24934, v24941, v24936, v24935, v24940, v24939, v24938, v24937, v24948, v11803, v11802, v11801, v11791, v11800, v11792, v11799, v11794, v11793, v11798, v11797, v11796, v11795, eq, QueueDestination1_0] using h0
  · have eq : s.g59.r1900_nringBufferTail = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24946, v24945, v24944, v24943, v24933, v24942, v24934, v24941, v24936, v24935, v24940, v24939, v24938, v24937, v24948, v11803, v11802, v11801, v11791, v11800, v11792, v11799, v11794, v11793, v11798, v11797, v11796, v11795, eq, QueueDestination1_1] using h1
  · have eq : s.g59.r1900_nringBufferTail = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24946, v24945, v24944, v24943, v24933, v24942, v24934, v24941, v24936, v24935, v24940, v24939, v24938, v24937, v24948, v11803, v11802, v11801, v11791, v11800, v11792, v11799, v11794, v11793, v11798, v11797, v11796, v11795, eq, QueueDestination1_2] using h2
  · have eq : s.g59.r1900_nringBufferTail = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24297, v24296, v24295, v24294, v24284, v2750, v24293, v24285, v9721, v24292, v24287, v24286, v24291, v24290, v24289, v24288, v110, v24946, v24945, v24944, v24943, v24933, v24942, v24934, v24941, v24936, v24935, v24940, v24939, v24938, v24937, v24948, v11803, v11802, v11801, v11791, v11800, v11792, v11799, v11794, v11793, v11798, v11797, v11796, v11795, eq, QueueDestination1_3] using h3

def ExecuteDestination1Decoded (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 → DestinationDecoded 7 s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr s.g48.r1557_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfWen s.g48.r1558_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fctrl_5FrfDest

theorem execute_destination1_step (s : State) (i : Inputs)
    (queue : QueueDestinations1Decoded s) (old : ExecuteDestination1Decoded s) :
    ExecuteDestination1Decoded (step s i) := by
  intro valid
  change DestinationDecoded 7 (v24298 s i) (v24947 s i) (v24949 s i)
  by_cases fire : v24283 s i = 1
  · simpa only [v24298, v24947, v24949, fire, ↓reduceIte, v24946, v24948] using queue_selected_destination1 s i queue
  · simp only [v24298, v24947, v24949, fire, ↓reduceIte]
    exact old (execute_valid_backward s i i valid fire)

def Destination1DecodeState (s : State) : Prop := QueueDestinations1Decoded s ∧ ExecuteDestination1Decoded s

theorem destination1_decode_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    Destination1DecodeState (step s i) := by
  constructor
  · exact ⟨queue_destination1_0_reset s i reset, queue_destination1_1_reset s i reset, queue_destination1_2_reset s i reset, queue_destination1_3_reset s i reset⟩
  · intro valid
    have zero := execute_valid_reset s i i reset
    change v6 (step s i) i = 1 at valid
    rw [zero] at valid
    contradiction

theorem destination1_decode_step (s : State) (i : Inputs) (old : Destination1DecodeState s) :
    Destination1DecodeState (step s i) := by
  rcases old with ⟨queue, exu⟩
  refine ⟨?_, execute_destination1_step s i queue exu⟩
  rcases queue with ⟨h0, h1, h2, h3⟩
  exact ⟨queue_destination1_0_step s i h0, queue_destination1_1_step s i h1, queue_destination1_2_step s i h2, queue_destination1_3_step s i h3⟩

theorem destination1_decode_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    Destination1DecodeState (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact destination1_decode_reset initial (inputs 0) reset
  | succ t ih => exact destination1_decode_step _ _ ih

#print axioms destination1_decode_run
end NutShellProofs
