import Proofs.QueueInstructionPC
import Proofs.IDUInstructionPC
namespace NutShellProofs
open nNutCore

def IDUInstructionPC (relation : BitVec 64 → BitVec 39 → Prop) (s : State) : Prop :=
  s.g38.r1241_nfrontend_5Fvalid = 1 →
    relation s.g38.r1242_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Finstr
      s.g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc

theorem idu_instruction_pc_relation_step (relation : BitVec 64 → BitVec 39 → Prop)
    (s : State) (i : Inputs) (old : IDUInstructionPC relation s)
    (source : v11102 s i = 1 → relation (v11105 s i) (v10174 s i)) :
    IDUInstructionPC relation (step s i) := by
  intro valid
  by_cases fire : v11102 s i = 1
  · rcases idu_instruction_pc_capture s i fire with ⟨instr, pc⟩
    rw [instr, pc]
    exact source fire
  · rcases idu_instruction_pc_hold s i fire with ⟨instr, pc⟩
    rw [instr, pc]
    apply old
    have noCapture : v11096 s i ≠ 1 := fire
    change v11101 s i = 1 at valid
    unfold v11101 at valid
    split at valid
    · simp [v24] at valid
    · unfold v11100 at valid
      split at valid
      · simp [v24] at valid
      · simp only [v11099, noCapture, ↓reduceIte] at valid
        unfold v11098 at valid
        split at valid
        · simp [v24] at valid
        · exact valid

def InstructionPCPipeline (relation : BitVec 64 → BitVec 39 → Prop) (s : State) : Prop :=
  IDUInstructionPC relation s ∧ QueueInstructionPC relation s ∧ EXUInstructionPC relation s

theorem instruction_pc_pipeline_reset (relation : BitVec 64 → BitVec 39 → Prop)
    (s : State) (i : Inputs) (zero : relation 0 0) (reset : i.g0.nreset = 1) :
    InstructionPCPipeline relation (step s i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro valid
    change v11101 s i = 1 at valid
    simp [v11101, v0, v24, reset] at valid
  · change relation (v26233 s i) (v26254 s i) ∧
      relation (v29247 s i) (v29257 s i) ∧
      relation (v29795 s i) (v29803 s i) ∧
      relation (v30235 s i) (v30243 s i)
    simpa [v26233, v26254, v29247, v29257, v29795, v29803,
      v30235, v30243, reset, v4051, v8200] using zero
  · intro valid
    have clear := execute_valid_reset s i i reset
    change (step s i).g47.r1511_nbackend_5Fvalid = 0 at clear
    rw [clear] at valid
    contradiction

theorem instruction_pc_pipeline_step (relation : BitVec 64 → BitVec 39 → Prop)
    (s : State) (i : Inputs) (zero : relation 0 0)
    (old : InstructionPCPipeline relation s)
    (source : v11102 s i = 1 → relation (v11105 s i) (v10174 s i)) :
    InstructionPCPipeline relation (step s i) := by
  rcases old with ⟨idu, queue, exu⟩
  exact ⟨idu_instruction_pc_relation_step relation s i idu source,
    queue_instruction_pc_step relation s i zero queue idu,
    exu_instruction_pc_step relation s i queue exu⟩

theorem instruction_pc_pipeline_run (relation : BitVec 64 → BitVec 39 → Prop)
    (initial : State) (inputs : Nat → Inputs) (zero : relation 0 0)
    (reset : (inputs 0).g0.nreset = 1)
    (source : ∀ t, v11102 (run initial inputs t) (inputs t) = 1 →
      relation (v11105 (run initial inputs t) (inputs t))
        (v10174 (run initial inputs t) (inputs t))) (t : Nat) :
    InstructionPCPipeline relation (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact instruction_pc_pipeline_reset relation initial (inputs 0) zero reset
  | succ t ih => exact instruction_pc_pipeline_step relation _ _ zero ih (source (t + 1))

#print axioms instruction_pc_pipeline_run

theorem instruction_pc_pipeline_prefix (relation : BitVec 64 → BitVec 39 → Prop)
    (initial : State) (inputs : Nat → Inputs) (zero : relation 0 0)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (source : ∀ k, k ≤ t → v11102 (run initial inputs k) (inputs k) = 1 →
      relation (v11105 (run initial inputs k) (inputs k))
        (v10174 (run initial inputs k) (inputs k))) :
    InstructionPCPipeline relation (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact instruction_pc_pipeline_reset relation initial (inputs 0) zero reset
  | succ t ih =>
    have previous := ih (fun k hk => source k (by omega))
    exact instruction_pc_pipeline_step relation _ _ zero previous (source (t + 1) (by omega))

/-- Every valid execute pair is either the reset pair or an earlier captured pair.
    Queue occupancy/order is still needed to exclude the reset alternative. -/
theorem execute_instruction_pc_origin (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : (run initial inputs (t + 1)).g47.r1511_nbackend_5Fvalid = 1) :
    let instr := (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr
    let pc := (run initial inputs (t + 1)).g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc
    (instr = 0 ∧ pc = 0) ∨ ∃ k, k ≤ t ∧
      v11102 (run initial inputs k) (inputs k) = 1 ∧
      instr = v11105 (run initial inputs k) (inputs k) ∧
      pc = v10174 (run initial inputs k) (inputs k) := by
  let relation := fun instr pc => (instr = (0 : BitVec 64) ∧ pc = (0 : BitVec 39)) ∨
    ∃ k, k ≤ t ∧ v11102 (run initial inputs k) (inputs k) = 1 ∧
      instr = v11105 (run initial inputs k) (inputs k) ∧
      pc = v10174 (run initial inputs k) (inputs k)
  have zero : relation 0 0 := Or.inl ⟨rfl, rfl⟩
  have pipeline := instruction_pc_pipeline_prefix relation initial inputs zero reset t
    (fun k bound capture => Or.inr ⟨k, bound, capture, rfl, rfl⟩)
  exact pipeline.2.2 valid

#print axioms instruction_pc_pipeline_prefix
#print axioms execute_instruction_pc_origin
end NutShellProofs
