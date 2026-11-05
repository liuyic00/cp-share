import Proofs.IDUNonAtomic
namespace NutShellProofs
open nNutCore

theorem non_atomic_instruction_ite (p : Prop) [Decidable p] (x y : BitVec 64)
    (hx : NonAtomicInstruction x) (hy : NonAtomicInstruction y) :
    NonAtomicInstruction (if p then x else y) := by
  by_cases h : p
  · simpa only [if_pos h] using hx
  · simpa only [if_neg h] using hy

theorem non_atomic_instruction_zero : NonAtomicInstruction 0 := by
  unfold NonAtomicInstruction
  decide

theorem queue_non_atomic_instruction_reset_0 (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    NonAtomicInstruction (step s i).g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr := by
  change NonAtomicInstruction (v26233 s i)
  simpa [v26233, reset, v4051] using non_atomic_instruction_zero
theorem queue_non_atomic_instruction_step_0 (s : State) (i : Inputs)
    (old : NonAtomicInstruction s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr) (idu : IDUNonAtomic s) :
    NonAtomicInstruction (step s i).g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr := by
  by_cases reset : i.g0.nreset = 1
  · exact queue_non_atomic_instruction_reset_0 s i reset
  · have nr : i.g0.nreset = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right reset
    rcases BitVec.eq_zero_or_eq_one (v9827 s i) with idle | valid
    · change NonAtomicInstruction (v26233 s i)
      simpa [v26233, v4051, v26209, v26210, v26211, v26212, v26213, v26222, v26223, v26224, v26225, v26226, v26227, v26228, v26229, v26230, v26231, v26232, v26233, v26198, v26189, v26197, v26193, v26192, v26191, v26190, v24, v26202, v26201, v26199, v26200, v9721, nr, idle] using old
    · have source : NonAtomicInstruction (v26226 s i) := idu valid
      change NonAtomicInstruction (v26233 s i)
      simp only [v4051, v26209, v26210, v26211, v26212, v26213, v26222, v26223, v26224, v26225, v26226, v26227, v26228, v26229, v26230, v26231, v26232, v26233] at source ⊢
      simp [v26198, v26189, v26197, v26193, v26192, v26191, v26190, v24, v26202, v26201, v26199, v26200, v9721, nr, valid]
      repeat' first | assumption | apply non_atomic_instruction_ite
theorem queue_non_atomic_instruction_reset_1 (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    NonAtomicInstruction (step s i).g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr := by
  change NonAtomicInstruction (v29247 s i)
  simpa [v29247, reset, v4051] using non_atomic_instruction_zero
theorem queue_non_atomic_instruction_step_1 (s : State) (i : Inputs)
    (old : NonAtomicInstruction s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr) (idu : IDUNonAtomic s) :
    NonAtomicInstruction (step s i).g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr := by
  by_cases reset : i.g0.nreset = 1
  · exact queue_non_atomic_instruction_reset_1 s i reset
  · have nr : i.g0.nreset = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right reset
    rcases BitVec.eq_zero_or_eq_one (v9827 s i) with idle | valid
    · change NonAtomicInstruction (v29247 s i)
      simpa [v29247, v4051, v26209, v26210, v26211, v26212, v26213, v26222, v26223, v26224, v26225, v26226, v26227, v29242, v29243, v29244, v29245, v29246, v29247, v26198, v26189, v26197, v26193, v26192, v26191, v26190, v24, v26202, v26201, v26199, v26200, v9721, nr, idle] using old
    · have source : NonAtomicInstruction (v26226 s i) := idu valid
      change NonAtomicInstruction (v29247 s i)
      simp only [v4051, v26209, v26210, v26211, v26212, v26213, v26222, v26223, v26224, v26225, v26226, v26227, v29242, v29243, v29244, v29245, v29246, v29247] at source ⊢
      simp [v26198, v26189, v26197, v26193, v26192, v26191, v26190, v24, v26202, v26201, v26199, v26200, v9721, nr, valid]
      repeat' first | assumption | apply non_atomic_instruction_ite
theorem queue_non_atomic_instruction_reset_2 (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    NonAtomicInstruction (step s i).g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr := by
  change NonAtomicInstruction (v29795 s i)
  simpa [v29795, reset, v4051] using non_atomic_instruction_zero
theorem queue_non_atomic_instruction_step_2 (s : State) (i : Inputs)
    (old : NonAtomicInstruction s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr) (idu : IDUNonAtomic s) :
    NonAtomicInstruction (step s i).g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr := by
  by_cases reset : i.g0.nreset = 1
  · exact queue_non_atomic_instruction_reset_2 s i reset
  · have nr : i.g0.nreset = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right reset
    rcases BitVec.eq_zero_or_eq_one (v9827 s i) with idle | valid
    · change NonAtomicInstruction (v29795 s i)
      simpa [v29795, v4051, v26209, v26210, v26211, v26212, v26213, v26222, v26223, v26224, v26225, v26226, v26227, v29790, v29791, v29792, v29793, v29794, v29795, v26198, v26189, v26197, v26193, v26192, v26191, v26190, v24, v26202, v26201, v26199, v26200, v9721, nr, idle] using old
    · have source : NonAtomicInstruction (v26226 s i) := idu valid
      change NonAtomicInstruction (v29795 s i)
      simp only [v4051, v26209, v26210, v26211, v26212, v26213, v26222, v26223, v26224, v26225, v26226, v26227, v29790, v29791, v29792, v29793, v29794, v29795] at source ⊢
      simp [v26198, v26189, v26197, v26193, v26192, v26191, v26190, v24, v26202, v26201, v26199, v26200, v9721, nr, valid]
      repeat' first | assumption | apply non_atomic_instruction_ite
theorem queue_non_atomic_instruction_reset_3 (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    NonAtomicInstruction (step s i).g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr := by
  change NonAtomicInstruction (v30235 s i)
  simpa [v30235, reset, v4051] using non_atomic_instruction_zero
theorem queue_non_atomic_instruction_step_3 (s : State) (i : Inputs)
    (old : NonAtomicInstruction s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr) (idu : IDUNonAtomic s) :
    NonAtomicInstruction (step s i).g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr := by
  by_cases reset : i.g0.nreset = 1
  · exact queue_non_atomic_instruction_reset_3 s i reset
  · have nr : i.g0.nreset = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right reset
    rcases BitVec.eq_zero_or_eq_one (v9827 s i) with idle | valid
    · change NonAtomicInstruction (v30235 s i)
      simpa [v30235, v4051, v26209, v26210, v26211, v26212, v26213, v26222, v26223, v26224, v26225, v26226, v26227, v30230, v30231, v30232, v30233, v30234, v30235, v26198, v26189, v26197, v26193, v26192, v26191, v26190, v24, v26202, v26201, v26199, v26200, v9721, nr, idle] using old
    · have source : NonAtomicInstruction (v26226 s i) := idu valid
      change NonAtomicInstruction (v30235 s i)
      simp only [v4051, v26209, v26210, v26211, v26212, v26213, v26222, v26223, v26224, v26225, v26226, v26227, v30230, v30231, v30232, v30233, v30234, v30235] at source ⊢
      simp [v26198, v26189, v26197, v26193, v26192, v26191, v26190, v24, v26202, v26201, v26199, v26200, v9721, nr, valid]
      repeat' first | assumption | apply non_atomic_instruction_ite
def QueueNonAtomic (s : State) : Prop :=
  NonAtomicInstruction s.g52.r1679_ndataBuffer_5F0_5Fcf_5Finstr ∧
  NonAtomicInstruction s.g54.r1734_ndataBuffer_5F1_5Fcf_5Finstr ∧
  NonAtomicInstruction s.g55.r1789_ndataBuffer_5F2_5Fcf_5Finstr ∧
  NonAtomicInstruction s.g57.r1844_ndataBuffer_5F3_5Fcf_5Finstr
theorem queue_selected_non_atomic_instruction (s : State) (i : Inputs)
    (queue : QueueNonAtomic s) : NonAtomicInstruction (v24297 s i) := by
  rcases queue with ⟨h0, h1, h2, h3⟩
  have bound := s.g59.r1900_nringBufferTail.isLt
  have cases : s.g59.r1900_nringBufferTail.toNat = 0 ∨ s.g59.r1900_nringBufferTail.toNat = 1 ∨ s.g59.r1900_nringBufferTail.toNat = 2 ∨ s.g59.r1900_nringBufferTail.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : s.g59.r1900_nringBufferTail = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24284, v24285, v24286, v24287, v24288, v24289, v24290, v24291, v24292, v24293, v24294, v24295, v24296, v24297, v2750, v9721, v110, eq] using h0
  · have eq : s.g59.r1900_nringBufferTail = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24284, v24285, v24286, v24287, v24288, v24289, v24290, v24291, v24292, v24293, v24294, v24295, v24296, v24297, v2750, v9721, v110, eq] using h1
  · have eq : s.g59.r1900_nringBufferTail = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24284, v24285, v24286, v24287, v24288, v24289, v24290, v24291, v24292, v24293, v24294, v24295, v24296, v24297, v2750, v9721, v110, eq] using h2
  · have eq : s.g59.r1900_nringBufferTail = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v24284, v24285, v24286, v24287, v24288, v24289, v24290, v24291, v24292, v24293, v24294, v24295, v24296, v24297, v2750, v9721, v110, eq] using h3
def EXUNonAtomic (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 →
    NonAtomicInstruction s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr

theorem exu_non_atomic_instruction_step (s : State) (i : Inputs)
    (queue : QueueNonAtomic s) (old : EXUNonAtomic s) :
    EXUNonAtomic (step s i) := by
  intro valid
  change NonAtomicInstruction (v24298 s i)
  by_cases fire : v24283 s i = 1
  · rw [v24298, if_pos fire]
    exact queue_selected_non_atomic_instruction s i queue
  · rw [v24298, if_neg fire]
    exact old (execute_valid_backward s i i valid fire)

def NonAtomicPipelineState (s : State) : Prop :=
  IDUNonAtomic s ∧ QueueNonAtomic s ∧ EXUNonAtomic s

theorem non_atomic_pipeline_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    NonAtomicPipelineState (step s i) := by
  refine ⟨idu_non_atomic_reset s i reset, ?_, ?_⟩
  · exact ⟨queue_non_atomic_instruction_reset_0 s i reset, queue_non_atomic_instruction_reset_1 s i reset, queue_non_atomic_instruction_reset_2 s i reset, queue_non_atomic_instruction_reset_3 s i reset⟩
  · intro valid
    have zero := execute_valid_reset s i i reset
    change (step s i).g47.r1511_nbackend_5Fvalid = 0 at zero
    rw [zero] at valid
    contradiction

theorem non_atomic_pipeline_step (s : State) (i : Inputs) (old : NonAtomicPipelineState s) (environment : assumes s i) :
    NonAtomicPipelineState (step s i) := by
  rcases old with ⟨idu, queue, exu⟩
  refine ⟨idu_non_atomic_step s i idu environment, ?_, exu_non_atomic_instruction_step s i queue exu⟩
  rcases queue with ⟨h0, h1, h2, h3⟩
  exact ⟨queue_non_atomic_instruction_step_0 s i h0 idu, queue_non_atomic_instruction_step_1 s i h1 idu, queue_non_atomic_instruction_step_2 s i h2 idu, queue_non_atomic_instruction_step_3 s i h3 idu⟩
theorem non_atomic_pipeline_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ t, assumes (run initial inputs t) (inputs t)) (t : Nat) :
    NonAtomicPipelineState (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact non_atomic_pipeline_reset initial (inputs 0) reset
  | succ t ih => exact non_atomic_pipeline_step _ _ ih (environment (t + 1))

#print axioms non_atomic_pipeline_run
end NutShellProofs
