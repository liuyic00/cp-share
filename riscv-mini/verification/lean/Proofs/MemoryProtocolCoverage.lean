import Proofs.MemoryProtocol
import Proofs.ReferenceMemoryProtocol
import Proofs.NonMemoryCorrectness
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem lui_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (lui_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, lui_store _ known] at width
  rw [decode_store_valid, decode_store_width, lui_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_lui_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms lui_memory_protocol
theorem auipc_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (auipc_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, auipc_store _ known] at width
  rw [decode_store_valid, decode_store_width, auipc_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_auipc_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms auipc_memory_protocol
theorem jal_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (jal_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, jal_store _ known] at width
  rw [decode_store_valid, decode_store_width, jal_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_jal_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms jal_memory_protocol
theorem jalr_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (jalr_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, jalr_store _ known] at width
  rw [decode_store_valid, decode_store_width, jalr_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_jalr_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms jalr_memory_protocol
theorem beq_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (beq_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, beq_store _ known] at width
  rw [decode_store_valid, decode_store_width, beq_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_beq_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms beq_memory_protocol
theorem bne_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (bne_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, bne_store _ known] at width
  rw [decode_store_valid, decode_store_width, bne_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_bne_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms bne_memory_protocol
theorem blt_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (blt_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, blt_store _ known] at width
  rw [decode_store_valid, decode_store_width, blt_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_blt_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms blt_memory_protocol
theorem bge_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (bge_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, bge_store _ known] at width
  rw [decode_store_valid, decode_store_width, bge_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_bge_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms bge_memory_protocol
theorem bltu_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (bltu_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, bltu_store _ known] at width
  rw [decode_store_valid, decode_store_width, bltu_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_bltu_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms bltu_memory_protocol
theorem bgeu_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (bgeu_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, bgeu_store _ known] at width
  rw [decode_store_valid, decode_store_width, bgeu_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_bgeu_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms bgeu_memory_protocol
theorem lb_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (lb_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, lb_store _ known] at width
  rw [decode_store_valid, decode_store_width, lb_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_lb_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms lb_memory_protocol
theorem lh_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (lh_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, lh_store _ known] at width
  rw [decode_store_valid, decode_store_width, lh_store _ known] at valid
  have aligned := reference_lh_memory_guard s i commit event known
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_lh_memory_protocol s i commit aligned known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms lh_memory_protocol
theorem lw_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (lw_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, lw_store _ known] at width
  rw [decode_store_valid, decode_store_width, lw_store _ known] at valid
  have aligned := reference_lw_memory_guard s i commit event known
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_lw_memory_protocol s i commit aligned known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms lw_memory_protocol
theorem lbu_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (lbu_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, lbu_store _ known] at width
  rw [decode_store_valid, decode_store_width, lbu_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_lbu_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms lbu_memory_protocol
theorem lhu_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (lhu_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, lhu_store _ known] at width
  rw [decode_store_valid, decode_store_width, lhu_store _ known] at valid
  have aligned := reference_lhu_memory_guard s i commit event known
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_lhu_memory_protocol s i commit aligned known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms lhu_memory_protocol
theorem sb_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (sb_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, sb_store _ known] at width
  rw [decode_store_valid, decode_store_width, sb_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sb_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms sb_memory_protocol
theorem sh_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (sh_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, sh_store _ known] at width
  rw [decode_store_valid, decode_store_width, sh_store _ known] at valid
  have aligned := reference_sh_memory_guard s i commit event known
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sh_memory_protocol s i commit aligned known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms sh_memory_protocol
theorem sw_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (sw_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, sw_store _ known] at width
  rw [decode_store_valid, decode_store_width, sw_store _ known] at valid
  have aligned := reference_sw_memory_guard s i commit event known
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sw_memory_protocol s i commit aligned known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms sw_memory_protocol
theorem addi_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (addi_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, addi_store _ known] at width
  rw [decode_store_valid, decode_store_width, addi_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_addi_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms addi_memory_protocol
theorem slti_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (slti_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, slti_store _ known] at width
  rw [decode_store_valid, decode_store_width, slti_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_slti_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms slti_memory_protocol
theorem sltiu_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (sltiu_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, sltiu_store _ known] at width
  rw [decode_store_valid, decode_store_width, sltiu_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sltiu_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms sltiu_memory_protocol
theorem xori_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (xori_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, xori_store _ known] at width
  rw [decode_store_valid, decode_store_width, xori_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_xori_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms xori_memory_protocol
theorem ori_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (ori_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, ori_store _ known] at width
  rw [decode_store_valid, decode_store_width, ori_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_ori_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms ori_memory_protocol
theorem andi_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (andi_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, andi_store _ known] at width
  rw [decode_store_valid, decode_store_width, andi_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_andi_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms andi_memory_protocol
theorem slli_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (slli_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, slli_store _ known] at width
  rw [decode_store_valid, decode_store_width, slli_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_slli_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms slli_memory_protocol
theorem srli_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (srli_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, srli_store _ known] at width
  rw [decode_store_valid, decode_store_width, srli_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_srli_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms srli_memory_protocol
theorem srai_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (srai_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, srai_store _ known] at width
  rw [decode_store_valid, decode_store_width, srai_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_srai_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms srai_memory_protocol
theorem add_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (add_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, add_store _ known] at width
  rw [decode_store_valid, decode_store_width, add_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_add_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms add_memory_protocol
theorem sub_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (sub_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, sub_store _ known] at width
  rw [decode_store_valid, decode_store_width, sub_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sub_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms sub_memory_protocol
theorem sll_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (sll_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, sll_store _ known] at width
  rw [decode_store_valid, decode_store_width, sll_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sll_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms sll_memory_protocol
theorem slt_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (slt_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, slt_store _ known] at width
  rw [decode_store_valid, decode_store_width, slt_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_slt_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms slt_memory_protocol
theorem sltu_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (sltu_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, sltu_store _ known] at width
  rw [decode_store_valid, decode_store_width, sltu_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sltu_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms sltu_memory_protocol
theorem xor_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (xor_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, xor_store _ known] at width
  rw [decode_store_valid, decode_store_width, xor_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_xor_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms xor_memory_protocol
theorem srl_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (srl_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, srl_store _ known] at width
  rw [decode_store_valid, decode_store_width, srl_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_srl_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms srl_memory_protocol
theorem sra_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (sra_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, sra_store _ known] at width
  rw [decode_store_valid, decode_store_width, sra_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sra_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms sra_memory_protocol
theorem or_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (or_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, or_store _ known] at width
  rw [decode_store_valid, decode_store_width, or_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_or_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms or_memory_protocol
theorem and_memory_protocol (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (control : MemoryControl s)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : MemoryProtocol s i := by
  have trap := environment_no_trap s i reset env
  have load := control.load.trans (and_load _ known)
  have width := control.width
  have valid := control.valid
  rw [decode_store_width, and_store _ known] at width
  rw [decode_store_valid, decode_store_width, and_store _ known] at valid
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_and_memory_protocol s i commit known
  constructor
  · rw [readValid]
    simp [v9156, v9155, v9153, v9152, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, v9154, load, trap, v4,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [readWidth]
    simp [v9176, v9151, v9150, v9149, v9148, v9147,
      v9146, v9145, v9144, v9143, v9142, load,
      v200, v26, v29, v716, v22, v1941, v8605, v8607, v8609]
  · rw [writeValid]
    simp [v9196, v9195, v9194, valid, trap, v4]
  · rw [writeWidth]
    simp [v9253, width]
#print axioms and_memory_protocol
theorem memory_protocol_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) : MemoryProtocol (run initial inputs t) (inputs t) := by
  have control := memory_control_reachable initial inputs cycles reset env t ht
  rcases BitVec.eq_zero_or_eq_one (v964 (run initial inputs t) (inputs t)) with idle | commit
  · exact memory_protocol_idle _ _ (reset.2.2 t ht) control
      (bubble_alignment_reachable initial inputs cycles reset env t ht) idle
  · have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
      (event_valid_reachable initial inputs cycles reset env t ht)
    have supported := environment_supported_at_commit _ _ (reset.2.2 t ht) (env t) commit
    cases supported with
    | op_add known => exact add_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_addi known => exact addi_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_and known => exact and_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_andi known => exact andi_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_auipc known => exact auipc_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_beq known => exact beq_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_bge known => exact bge_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_bgeu known => exact bgeu_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_blt known => exact blt_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_bltu known => exact bltu_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_bne known => exact bne_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_jal known => exact jal_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_jalr known => exact jalr_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_lb known => exact lb_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_lbu known => exact lbu_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_lh known => exact lh_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_lhu known => exact lhu_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_lui known => exact lui_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_lw known => exact lw_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_or known => exact or_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_ori known => exact ori_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_sb known => exact sb_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_sh known => exact sh_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_sll known => exact sll_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_slli known => exact slli_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_slt known => exact slt_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_slti known => exact slti_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_sltiu known => exact sltiu_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_sltu known => exact sltu_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_sra known => exact sra_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_srai known => exact srai_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_srl known => exact srl_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_srli known => exact srli_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_sub known => exact sub_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_sw known => exact sw_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_xor known => exact xor_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known
    | op_xori known => exact xori_memory_protocol _ _ (reset.2.2 t ht) (env t) control commit event known

theorem memory_protocol_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) : MemoryProtocolTasks (run initial inputs t) (inputs t) :=
  memory_protocol_tasks _ _ (memory_protocol_reachable initial inputs cycles reset env t ht)
#print axioms memory_protocol_reachable
#print axioms memory_protocol_tasks_reachable
end RiscvMiniProofs
