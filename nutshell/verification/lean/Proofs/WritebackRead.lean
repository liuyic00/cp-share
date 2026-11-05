import Proofs.IssueReadiness
import Proofs.RegisterReadStep
namespace NutShellProofs
open nNutCore
theorem captured_writeback_1_equals_register (s : State) (i next : Inputs)
    (fire : v24283 s i = 1) (ex : v11741 s i = 0) (wb : v11750 s i = 1)
    (kind : v24881 s i = 0) (reset : i.g0.nreset = 0) :
    (step s i).g48.r1564_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc1 =
      dutRead.v25201 (step s i) next (v11723 s i) := by
  obtain ⟨nonzero, dest, write⟩ := writeback_forward_1_matches s i wb
  rw [operand_1_capture s i fire, operand_1_writeback s i kind ex wb,
    dut_read_step s i next _ reset, if_neg nonzero, if_pos ⟨dest.symm, write⟩]

#print axioms captured_writeback_1_equals_register
theorem captured_writeback_2_equals_register (s : State) (i next : Inputs)
    (fire : v24283 s i = 1) (ex : v11776 s i = 0) (wb : v11785 s i = 1)
    (kind : v24896 s i = 0) (reset : i.g0.nreset = 0) :
    (step s i).g48.r1565_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc2 =
      dutRead.v25201 (step s i) next (v11765 s i) := by
  obtain ⟨nonzero, dest, write⟩ := writeback_forward_2_matches s i wb
  rw [operand_2_capture s i fire, operand_2_writeback s i kind ex wb,
    dut_read_step s i next _ reset, if_neg nonzero, if_pos ⟨dest.symm, write⟩]

#print axioms captured_writeback_2_equals_register
end NutShellProofs
