From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedDivisionTrace MulDivCheckedSignedTimingTrace MulDivCheckedUnsignedTiming MulDivCheckedDivisionOutput.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory MulDivCheckedLatency.MulDivCheckedLatency.
Open Scope Z_scope.
Module MulDivCheckedDivisionSign.
Module D := MulDivCheckedDivisionTrace.MulDivCheckedDivisionTrace.
Module S := MulDivCheckedSignedTimingTrace.MulDivCheckedSignedTimingTrace.
Module U := MulDivCheckedUnsignedTiming.MulDivCheckedUnsignedTiming.
Definition SignInvariant s := word 1 (r9_ncontractPending s)=1 -> D.Operation s ->
  (word 3 (r0_nstate s)=3 -> word 7 (r3_ncount s)=64 -> word 1 (r4_nneg_5Fout s)=outputExtra s) /\
  (word 3 (r0_nstate s)=5 -> outputExtra s=1).
Lemma unsigned_negative s (op : U.Operation s) : outputExtra s=0.
Proof.
  assert (sign : v194 s quiet=0) by (unfold v194,v193,v31; destruct op as [fn|fn]; rewrite fn; reflexivity).
  assert (a : v202 s quiet=0) by (unfold v202; rewrite sign,Z.land_0_l; reflexivity).
  assert (b : v210 s quiet=0) by (unfold v210; rewrite sign,Z.land_0_l; reflexivity).
  unfold outputExtra,v219,v218,v214; rewrite a,b.
  change (word 1 (if v213 s quiet=?1 then 0 else word 1 (Z.land 0 (v217 s quiet)))=0).
  rewrite Z.land_0_l; destruct (v213 s quiet=?1); reflexivity.
Qed.
Theorem sign_invariant s (signed : S.Invariant s) (unsigned : U.Invariant s) : SignInvariant s.
Proof.
  intros pending op.
  assert (cases : MulDivCheckedSignedTiming.MulDivCheckedSignedTiming.Operation s \/ U.Operation s)
    by (unfold D.Operation in op; unfold MulDivCheckedSignedTiming.MulDivCheckedSignedTiming.Operation,U.Operation; intuition).
  destruct cases as [operation|operation].
  - pose proof (signed pending operation) as phases.
    unfold S.Phases,MulDivCheckedSignedTimingInit.MulDivCheckedSignedTimingInit.Negating,
      MulDivCheckedSignedTimingInit.MulDivCheckedSignedTimingInit.Prepared,
      MulDivCheckedSignedTimingEdges.MulDivCheckedSignedTimingEdges.LatePhases in phases.
    split; intros; intuition congruence.
  - pose proof (unsigned pending operation) as phases; pose proof (unsigned_negative s operation) as negative.
    unfold U.Phase in phases; split; intros; intuition congruence.
Qed.
Theorem signs_after_reset initial resetInput (reset : word 1 (nreset resetInput)=1) pins n :
  SignInvariant (run (step initial resetInput) pins n).
Proof. apply sign_invariant; [apply S.run_invariant|apply U.run_invariant]; exact reset. Qed.
End MulDivCheckedDivisionSign.
Print Assumptions MulDivCheckedDivisionSign.signs_after_reset.
