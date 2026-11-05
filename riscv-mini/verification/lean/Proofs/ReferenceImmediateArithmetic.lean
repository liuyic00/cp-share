import Proofs.ImmediateExecution
import Proofs.ReferenceExecution
namespace RiscvMiniProofs
open nCoreSoc
theorem reference_addi_cone (s : State) (i : Inputs) :
    v2351 s i = refExec_v2303 (v1721 s i) (v2092 s i) := by rfl
theorem decoded_reference_immediate_addi (s : State) (i : Inputs)
    (instruction pc rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19)
    (immediate : v2092 s i = immediateI instruction) :
    decodedExecution instruction pc (v1721 s i) rs2 = v2351 s i := by
  rw [reference_addi_cone, reference_execution_add, immediate]
  simpa [aluSpec, immediateI_low5] using decoded_execution_addi instruction pc (v1721 s i) rs2 known
#print axioms decoded_reference_immediate_addi
theorem reference_slti_cone (s : State) (i : Inputs) :
    v2345 s i = refExec_v2297 (v1721 s i) (v2092 s i) := by rfl
theorem decoded_reference_immediate_slti (s : State) (i : Inputs)
    (instruction pc rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211)
    (immediate : v2092 s i = immediateI instruction) :
    decodedExecution instruction pc (v1721 s i) rs2 = v2345 s i := by
  rw [reference_slti_cone, reference_execution_slt, immediate]
  simpa [aluSpec, immediateI_low5] using decoded_execution_slti instruction pc (v1721 s i) rs2 known
#print axioms decoded_reference_immediate_slti
theorem reference_sltiu_cone (s : State) (i : Inputs) :
    v2341 s i = refExec_v2293 (v1721 s i) (v2092 s i) := by rfl
theorem decoded_reference_immediate_sltiu (s : State) (i : Inputs)
    (instruction pc rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307)
    (immediate : v2092 s i = immediateI instruction) :
    decodedExecution instruction pc (v1721 s i) rs2 = v2341 s i := by
  rw [reference_sltiu_cone, reference_execution_sltu, immediate]
  simpa [aluSpec, immediateI_low5] using decoded_execution_sltiu instruction pc (v1721 s i) rs2 known
#print axioms decoded_reference_immediate_sltiu
theorem reference_xori_cone (s : State) (i : Inputs) :
    v2331 s i = refExec_v2283 (v1721 s i) (v2092 s i) := by rfl
theorem decoded_reference_immediate_xori (s : State) (i : Inputs)
    (instruction pc rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403)
    (immediate : v2092 s i = immediateI instruction) :
    decodedExecution instruction pc (v1721 s i) rs2 = v2331 s i := by
  rw [reference_xori_cone, reference_execution_xor, immediate]
  simpa [aluSpec, immediateI_low5] using decoded_execution_xori instruction pc (v1721 s i) rs2 known
#print axioms decoded_reference_immediate_xori
theorem reference_ori_cone (s : State) (i : Inputs) :
    v2334 s i = refExec_v2286 (v1721 s i) (v2092 s i) := by rfl
theorem decoded_reference_immediate_ori (s : State) (i : Inputs)
    (instruction pc rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595)
    (immediate : v2092 s i = immediateI instruction) :
    decodedExecution instruction pc (v1721 s i) rs2 = v2334 s i := by
  rw [reference_ori_cone, reference_execution_or, immediate]
  simpa [aluSpec, immediateI_low5] using decoded_execution_ori instruction pc (v1721 s i) rs2 known
#print axioms decoded_reference_immediate_ori
theorem reference_andi_cone (s : State) (i : Inputs) :
    v2337 s i = refExec_v2289 (v1721 s i) (v2092 s i) := by rfl
theorem decoded_reference_immediate_andi (s : State) (i : Inputs)
    (instruction pc rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691)
    (immediate : v2092 s i = immediateI instruction) :
    decodedExecution instruction pc (v1721 s i) rs2 = v2337 s i := by
  rw [reference_andi_cone, reference_execution_and, immediate]
  simpa [aluSpec, immediateI_low5] using decoded_execution_andi instruction pc (v1721 s i) rs2 known
#print axioms decoded_reference_immediate_andi
theorem reference_slli_cone (s : State) (i : Inputs) :
    v2328 s i = refExec_v2280 (v1721 s i) (v2092 s i) := by rfl
theorem decoded_reference_immediate_slli (s : State) (i : Inputs)
    (instruction pc rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115)
    (immediate : v2092 s i = immediateI instruction) :
    decodedExecution instruction pc (v1721 s i) rs2 = v2328 s i := by
  rw [reference_slli_cone, reference_execution_sll, immediate]
  simpa [aluSpec, immediateI_low5] using decoded_execution_slli instruction pc (v1721 s i) rs2 known
#print axioms decoded_reference_immediate_slli
theorem reference_srli_cone (s : State) (i : Inputs) :
    v2321 s i = refExec_v2271 (v1721 s i) (v2092 s i) := by rfl
theorem decoded_reference_immediate_srli (s : State) (i : Inputs)
    (instruction pc rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499)
    (immediate : v2092 s i = immediateI instruction) :
    decodedExecution instruction pc (v1721 s i) rs2 = v2321 s i := by
  rw [reference_srli_cone, reference_execution_srl, immediate]
  simpa [aluSpec, immediateI_low5] using decoded_execution_srli instruction pc (v1721 s i) rs2 known
#print axioms decoded_reference_immediate_srli
theorem reference_srai_cone (s : State) (i : Inputs) :
    v2316 s i = refExec_v2260 (v1721 s i) (v2092 s i) := by rfl
theorem decoded_reference_immediate_srai (s : State) (i : Inputs)
    (instruction pc rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323)
    (immediate : v2092 s i = immediateI instruction) :
    decodedExecution instruction pc (v1721 s i) rs2 = v2316 s i := by
  rw [reference_srai_cone, reference_execution_sra, immediate]
  simpa [aluSpec, immediateI_low5] using decoded_execution_srai instruction pc (v1721 s i) rs2 known
#print axioms decoded_reference_immediate_srai
end RiscvMiniProofs
