import Proofs.AddiWriteback
import Proofs.ReferenceAddiRegisters
import Proofs.CommittedDestination
namespace NutShellProofs
open nNutCore

/-- Conditional state preservation. Destination and write enable are explicit
remaining control obligations; the result equality refers to actual circuit nodes. -/
theorem addi_registers_aligned_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (addi : v14575 s i &&& BitVec.ofNat 32 28799 = BitVec.ofNat 32 19)
    (aligned : ArchitecturalRegistersAligned s)
    (destination : v11465 s i = v15142 s i)
    (write : v11462 s i = 1) (result : v11842 s i = v16585 s i) :
    ArchitecturalRegistersAligned (step s i) := by

  rcases aligned with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [reference_addi_register_1 s i reset commit addi]
    by_cases dest : v11465 s i = 1
    · rw [dut_register_write_1 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_1 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h1
  · rw [reference_addi_register_2 s i reset commit addi]
    by_cases dest : v11465 s i = 2
    · rw [dut_register_write_2 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_2 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h2
  · rw [reference_addi_register_3 s i reset commit addi]
    by_cases dest : v11465 s i = 3
    · rw [dut_register_write_3 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_3 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h3
  · rw [reference_addi_register_4 s i reset commit addi]
    by_cases dest : v11465 s i = 4
    · rw [dut_register_write_4 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_4 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h4
  · rw [reference_addi_register_5 s i reset commit addi]
    by_cases dest : v11465 s i = 5
    · rw [dut_register_write_5 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_5 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h5
  · rw [reference_addi_register_6 s i reset commit addi]
    by_cases dest : v11465 s i = 6
    · rw [dut_register_write_6 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_6 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h6
  · rw [reference_addi_register_7 s i reset commit addi]
    by_cases dest : v11465 s i = 7
    · rw [dut_register_write_7 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_7 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h7
  · rw [reference_addi_register_8 s i reset commit addi]
    by_cases dest : v11465 s i = 8
    · rw [dut_register_write_8 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_8 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h8
  · rw [reference_addi_register_9 s i reset commit addi]
    by_cases dest : v11465 s i = 9
    · rw [dut_register_write_9 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_9 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h9
  · rw [reference_addi_register_10 s i reset commit addi]
    by_cases dest : v11465 s i = 10
    · rw [dut_register_write_10 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_10 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h10
  · rw [reference_addi_register_11 s i reset commit addi]
    by_cases dest : v11465 s i = 11
    · rw [dut_register_write_11 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_11 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h11
  · rw [reference_addi_register_12 s i reset commit addi]
    by_cases dest : v11465 s i = 12
    · rw [dut_register_write_12 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_12 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h12
  · rw [reference_addi_register_13 s i reset commit addi]
    by_cases dest : v11465 s i = 13
    · rw [dut_register_write_13 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_13 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h13
  · rw [reference_addi_register_14 s i reset commit addi]
    by_cases dest : v11465 s i = 14
    · rw [dut_register_write_14 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_14 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h14
  · rw [reference_addi_register_15 s i reset commit addi]
    by_cases dest : v11465 s i = 15
    · rw [dut_register_write_15 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_15 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h15
  · rw [reference_addi_register_16 s i reset commit addi]
    by_cases dest : v11465 s i = 16
    · rw [dut_register_write_16 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_16 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h16
  · rw [reference_addi_register_17 s i reset commit addi]
    by_cases dest : v11465 s i = 17
    · rw [dut_register_write_17 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_17 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h17
  · rw [reference_addi_register_18 s i reset commit addi]
    by_cases dest : v11465 s i = 18
    · rw [dut_register_write_18 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_18 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h18
  · rw [reference_addi_register_19 s i reset commit addi]
    by_cases dest : v11465 s i = 19
    · rw [dut_register_write_19 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_19 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h19
  · rw [reference_addi_register_20 s i reset commit addi]
    by_cases dest : v11465 s i = 20
    · rw [dut_register_write_20 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_20 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h20
  · rw [reference_addi_register_21 s i reset commit addi]
    by_cases dest : v11465 s i = 21
    · rw [dut_register_write_21 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_21 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h21
  · rw [reference_addi_register_22 s i reset commit addi]
    by_cases dest : v11465 s i = 22
    · rw [dut_register_write_22 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_22 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h22
  · rw [reference_addi_register_23 s i reset commit addi]
    by_cases dest : v11465 s i = 23
    · rw [dut_register_write_23 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_23 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h23
  · rw [reference_addi_register_24 s i reset commit addi]
    by_cases dest : v11465 s i = 24
    · rw [dut_register_write_24 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_24 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h24
  · rw [reference_addi_register_25 s i reset commit addi]
    by_cases dest : v11465 s i = 25
    · rw [dut_register_write_25 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_25 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h25
  · rw [reference_addi_register_26 s i reset commit addi]
    by_cases dest : v11465 s i = 26
    · rw [dut_register_write_26 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_26 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h26
  · rw [reference_addi_register_27 s i reset commit addi]
    by_cases dest : v11465 s i = 27
    · rw [dut_register_write_27 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_27 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h27
  · rw [reference_addi_register_28 s i reset commit addi]
    by_cases dest : v11465 s i = 28
    · rw [dut_register_write_28 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_28 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h28
  · rw [reference_addi_register_29 s i reset commit addi]
    by_cases dest : v11465 s i = 29
    · rw [dut_register_write_29 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_29 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h29
  · rw [reference_addi_register_30 s i reset commit addi]
    by_cases dest : v11465 s i = 30
    · rw [dut_register_write_30 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_30 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h30
  · rw [reference_addi_register_31 s i reset commit addi]
    by_cases dest : v11465 s i = 31
    · rw [dut_register_write_31 s i reset dest write, result]
      simp only [← destination, dest, ↓reduceIte]
    · rw [dut_register_frame_31 s i reset dest]
      simpa only [← destination, dest, ↓reduceIte] using h31

/-- Run-level ADDI preservation uses the proved arithmetic correspondence.
Control and datapath correspondence are derived from reset and ADDI/ALU dispatch. -/
theorem addi_registers_aligned_run_step (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (addi : IsADDI (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    ArchitecturalRegistersAligned (run initial inputs (t + 3)) := by
  have matched : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&&
      BitVec.ofNat 32 28799 = BitVec.ofNat 32 19 := by
    have instr : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
        BitVec.extractLsb' 0 32 (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr :=
      committed_reference_instruction _ _ _ commit
    rw [instr]
    exact addi_match_low32 _ addi
  have write := writeback_addi_enabled_run initial inputs reset t commit unit addi
  have destination := committed_addi_destination_agrees _ _ _
    (destination1_decode_run initial inputs reset t).2 commit write addi
  exact addi_registers_aligned_step _ _ currentReset commit matched aligned destination write
    (writeback_addi_matches_reference_run initial inputs reset t commit unit addi aligned)
#print axioms addi_registers_aligned_step
#print axioms addi_registers_aligned_run_step
end NutShellProofs
