From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixTemporal RadixBalance RadixSetup RadixShift RadixInitialization RadixExecution RadixResult RadixZeroAccepted.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixTemporal.RadixTemporal RadixBalance.RadixBalance
  RadixSetup.RadixSetup RadixShift.RadixShift RadixInitialization.RadixInitialization
  RadixExecution.RadixExecution RadixResult.RadixResult RadixZeroAccepted.RadixZeroAccepted.
Open Scope Z_scope.
Module RadixSetupResult.
Local Opaque step run.
Theorem setup_computes s log shift inputs a n
  (hs : word 3 (r0_nstate s) = 1)
  (hr : word 1 (nreset log) = 0) (hj : word 1 (nreset shift) = 0)
  (nonzero : word 64 (r5_nbReg s) <> 0)
  (flag : word 1 (r1_ndivBy0Reg s) = 0)
  (doubled : word 65 (r6_naValx2Reg s) = 2*a)
  (count : word 6 (r9_ncnt_5Fvalue (step (step s log) shift)) + Z.of_nat n = 64)
  (reset : forall t, (t < n)%nat -> word 1 (nreset (inputs t)) = 0) :
  nio_5Fout_5Fvalid (observe (run (step (step s log) shift) inputs n) (inputs n)) = 1 /\
  v40 (run (step (step s log) shift) inputs n) (inputs n) = a / word 64 (r5_nbReg s) /\
  v402 (run (step (step s log) shift) inputs n) (inputs n) = a mod word 64 (r5_nbReg s) /\
  captured (run (step (step s log) shift) inputs n) = captured s.
Proof.
  set (u := step (step s log) shift) in *.
  assert (hu : word 3 (r0_nstate u) = 3).
  { unfold u; rewrite shift_state; [reflexivity | exact hj |].
    rewrite (log2_state s log hr hs); reflexivity. }
  pose proof (setup_captured s log shift hs hr) as kept.
  change (captured u = captured s) in kept.
  destruct (captured_operands u s kept) as [divisor dividend].
  assert (bound : RadixDatapath.RadixDatapath.candidate (r2_nshiftReg u) < 2*word 64 (r5_nbReg u)).
  { rewrite divisor; exact (skip_initializes_bound s log shift hs hr nonzero flag). }
  pose proof (setup_alignment s log shift n a hs hr hj doubled count) as aligned.
  change (2^Z.of_nat n * word 129 (r2_nshiftReg u) = 2*base*a) in aligned.
  destruct (compute_finished_result n u inputs a hu count reset bound aligned) as [hv [hq hrem]].
  rewrite divisor in hq, hrem.
  split; [exact hv | split; [exact hq | split; [exact hrem |]]].
  rewrite (compute_captured_run n u inputs hu ltac:(lia) reset); exact kept.
Qed.
End RadixSetupResult.
Print Assumptions RadixSetupResult.setup_computes.
