import Proofs.Forwarding
import Proofs.RegisterReads
import Proofs.RegisterReads2
namespace NutShellProofs
open nNutCore
theorem operand_1_register (s : State) (i : Inputs)
    (kind : v24881 s i = 0) (ex : v11741 s i = 0) (wb : v11750 s i = 0) :
    v25205 s i = v25201 s i := by
  simp [v24, v110, v24999, v25003, v25004, v25104, v25105, v25106, v25107, v25108, v25109, v25110, v25111, v25112, v25113, v25114, v25115, v25116, v25202, v25203, v25204, v25205, kind, ex, wb]
theorem operand_1_execute (s : State) (i : Inputs)
    (kind : v24881 s i = 0) (ex : v11741 s i = 1) :
    v25205 s i = v25103 s i := by
  simp [v24, v110, v24999, v25003, v25004, v25104, v25105, v25106, v25107, v25108, v25109, v25110, v25111, v25112, v25113, v25114, v25115, v25116, v25202, v25203, v25204, v25205, kind, ex]
theorem operand_1_writeback (s : State) (i : Inputs)
    (kind : v24881 s i = 0) (ex : v11741 s i = 0) (wb : v11750 s i = 1) :
    v25205 s i = v11842 s i := by
  simp [v24, v110, v24999, v25003, v25004, v25104, v25105, v25106, v25107, v25108, v25109, v25110, v25111, v25112, v25113, v25114, v25115, v25116, v25202, v25203, v25204, v25205, kind, ex, wb]
theorem operand_1_pc (s : State) (i : Inputs)
    (kind : v24881 s i = 1) (ex : v11741 s i = 0) (wb : v11750 s i = 0) :
    v25205 s i = v25002 s i := by
  simp [v24, v110, v24999, v25003, v25004, v25104, v25105, v25106, v25107, v25108, v25109, v25110, v25111, v25112, v25113, v25114, v25115, v25116, v25202, v25203, v25204, v25205, kind, ex, wb]
theorem operand_1_capture (s : State) (i : Inputs) (fire : v24283 s i = 1) :
    (step s i).g48.r1564_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc1 = v25205 s i := by
  change v25206 s i = v25205 s i
  simp [v25206, fire]
theorem operand_1_execute_writeback (s : State) (i next : Inputs)
    (kind : v24881 s i = 0) (ex : v11741 s i = 1)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0 ∨ v3 s i = 1) :
    v25205 s i = v11842 (step s i) next := by
  rw [operand_1_execute s i kind ex]
  exact forward_matches_writeback s i next commit unit
#print axioms operand_1_execute_writeback
theorem operand_2_register (s : State) (i : Inputs)
    (kind : v24896 s i = 0) (ex : v11776 s i = 0) (wb : v11785 s i = 0) :
    v25324 s i = v25320 s i := by
  simp [v24, v25207, v25221, v25222, v25223, v25224, v25225, v25226, v25227, v25228, v25229, v25230, v25231, v25232, v25233, v25234, v25235, v25321, v25322, v25323, v25324, kind, ex, wb]
theorem operand_2_execute (s : State) (i : Inputs)
    (kind : v24896 s i = 0) (ex : v11776 s i = 1) :
    v25324 s i = v25103 s i := by
  simp [v24, v25207, v25221, v25222, v25223, v25224, v25225, v25226, v25227, v25228, v25229, v25230, v25231, v25232, v25233, v25234, v25235, v25321, v25322, v25323, v25324, kind, ex]
theorem operand_2_writeback (s : State) (i : Inputs)
    (kind : v24896 s i = 0) (ex : v11776 s i = 0) (wb : v11785 s i = 1) :
    v25324 s i = v11842 s i := by
  simp [v24, v25207, v25221, v25222, v25223, v25224, v25225, v25226, v25227, v25228, v25229, v25230, v25231, v25232, v25233, v25234, v25235, v25321, v25322, v25323, v25324, kind, ex, wb]
theorem operand_2_immediate (s : State) (i : Inputs)
    (kind : v24896 s i = 1) (ex : v11776 s i = 0) (wb : v11785 s i = 0) :
    v25324 s i = v25220 s i := by
  simp [v24, v25207, v25221, v25222, v25223, v25224, v25225, v25226, v25227, v25228, v25229, v25230, v25231, v25232, v25233, v25234, v25235, v25321, v25322, v25323, v25324, kind, ex, wb]
theorem operand_2_capture (s : State) (i : Inputs) (fire : v24283 s i = 1) :
    (step s i).g48.r1565_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc2 = v25324 s i := by
  change v25325 s i = v25324 s i
  simp [v25325, fire]
theorem operand_2_execute_writeback (s : State) (i next : Inputs)
    (kind : v24896 s i = 0) (ex : v11776 s i = 1)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0 ∨ v3 s i = 1) :
    v25324 s i = v11842 (step s i) next := by
  rw [operand_2_execute s i kind ex]
  exact forward_matches_writeback s i next commit unit
#print axioms operand_2_execute_writeback
end NutShellProofs
