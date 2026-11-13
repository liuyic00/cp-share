From Stdlib Require Import ZArith Lia List Bool Zmod.Bits.
From BitsGenerated Require Import MultiCycleMac.
From BitsProofs Require Import BitFacts MultiCycleMac.
Import BitsGenerated.MultiCycleMac.nMultiCycleMac MultiCycleMacProofs.
Open Scope Z_scope.
Module MacInvariant.
Definition Invariant (s : State) : Prop :=
  ((r0_nstate s=bits.of_Z 2 2 \/ r0_nstate s=bits.of_Z 2 3) ->
    r4_nsum s=sum8 (r1_noperands_5Fa s) (r2_noperands_5Fb s)) /\
  (r0_nstate s=bits.of_Z 2 3 -> r5_nresult s=
    arithmetic (r1_noperands_5Fa s) (r2_noperands_5Fb s) (r3_noperands_5Fc s)) /\
  (r6_naccepted s=Zmod.one -> r0_nstate s=bits.of_Z 2 1) /\
  (r7_nwasAdding s=Zmod.one -> r0_nstate s=bits.of_Z 2 2) /\
  (r8_nwasMultiplying s=Zmod.one -> r0_nstate s=bits.of_Z 2 3) /\
  (r9_nstalled s=Zmod.one -> r0_nstate s=bits.of_Z 2 3 /\ r10_npreviousOutput s=r5_nresult s).
Ltac unfold_mac := unfold step,observe;
  cbn [r0_nstate r1_noperands_5Fa r2_noperands_5Fb r3_noperands_5Fc r4_nsum r5_nresult r6_naccepted r7_nwasAdding r8_nwasMultiplying r9_nstalled r10_npreviousOutput nio_5Fin_5Fready nio_5Fout_5Fvalid nio_5Fout_5Fbits];
  unfold v60, v59, v58, v57, v56, v55, v54, v53, v52, v51, v50, v49, v48, v47, v46, v45, v44, v43, v42, v41, v40, v39, v38, v37, v36, v35, v34, v33, v32, v31, v30, v29, v28, v27, v26, v25, v24, v23, v22, v21, v20, v19, v18, v17, v16, v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0.
Lemma state_cases (x : bits 2) : x=bits.of_Z 2 0 \/ x=bits.of_Z 2 1 \/ x=bits.of_Z 2 2 \/ x=bits.of_Z 2 3.
Proof.
  pose proof (bits.unsigned_range x ltac:(lia)) as bound.
  change (0<=Zmod.unsigned x<4) in bound.
  assert (cases : Zmod.unsigned x=0 \/ Zmod.unsigned x=1 \/ Zmod.unsigned x=2 \/ Zmod.unsigned x=3) by lia.
  destruct cases as [h|[h|[h|h]]]; [left|right;left|right;right;left|right;right;right];
    apply Zmod.to_Z_inj; rewrite bits.unsigned_of_Z; rewrite h; reflexivity.
Qed.
Local Opaque Zmod.app Zmod.add Zmod.mul.
Theorem reset_invariant s i (reset : nreset i=Zmod.one) : Invariant (step s i).
Proof.
  unfold Invariant; unfold_mac; rewrite reset; cbn [Zmod.eqb]; intuition discriminate.
Qed.
Theorem invariant_step s i (previous : Invariant s) : Invariant (step s i).
Proof.
  destruct (state_cases (r0_nstate s)) as [st|[st|[st|st]]];
  destruct (bit_cases (nreset i)) as [reset|reset];
  destruct (bit_cases (nio_5Fin_5Fvalid i)) as [valid|valid];
  destruct (bit_cases (nio_5Fout_5Fready i)) as [ready|ready];
  unfold Invariant in *; unfold_mac; rewrite st,reset,valid,ready;
  unfold arithmetic,product,sum8 in *;
  rewrite st in previous;
  cbv beta iota zeta delta -[Zmod.app Zmod.add Zmod.mul] in *;
  intuition congruence.
Qed.
Theorem invariant_asserts s i (previous : Invariant s) : asserts s i.
Proof.
  destruct s as [state a b c sum result accepted wasAdding wasMultiplying stalled previousOutput].
  destruct i as [resetPin validPin ina inb inc readyPin].
  unfold Invariant in previous;
    cbn [r0_nstate r1_noperands_5Fa r2_noperands_5Fb r3_noperands_5Fc r4_nsum r5_nresult r6_naccepted r7_nwasAdding r8_nwasMultiplying r9_nstalled r10_npreviousOutput] in previous.
  destruct previous as [hs [hp [h1 [h2 [h3 h4]]]]].
  destruct (state_cases state) as [st|[st|[st|st]]];
  destruct (bit_cases accepted) as [ha|ha];
  destruct (bit_cases wasAdding) as [hb|hb];
  destruct (bit_cases wasMultiplying) as [hc|hc];
  destruct (bit_cases stalled) as [hd|hd];
  subst state accepted wasAdding wasMultiplying stalled;
  try specialize (h1 eq_refl); try specialize (h2 eq_refl);
  try specialize (h3 eq_refl); try specialize (h4 eq_refl);
  try discriminate;
  try specialize (hs (or_introl eq_refl));
  try specialize (hs (or_intror eq_refl));
  try specialize (hp eq_refl);
  lazymatch type of h4 with _ /\ _ => destruct h4 as [phase h4] | _ => idtac end; try discriminate;
  try subst sum; try subst result; try subst previousOutput;
  destruct (bit_cases resetPin) as [reset|reset]; subst resetPin;
  unfold asserts,assertionChecks; unfold_mac;
  cbn [r0_nstate r1_noperands_5Fa r2_noperands_5Fb r3_noperands_5Fc r4_nsum r5_nresult r6_naccepted r7_nwasAdding r8_nwasMultiplying r9_nstalled r10_npreviousOutput nreset nio_5Fin_5Fvalid nio_5Fin_5Fbits_5Fa nio_5Fin_5Fbits_5Fb nio_5Fin_5Fbits_5Fc nio_5Fout_5Fready];
  unfold arithmetic,product,sum8.
  all: repeat first [progress rewrite Z.eqb_refl | progress cbn beta iota zeta |
    match goal with |- context[if ?test then _ else _] =>
      tryif (match goal with x : _ |- _ =>
        lazymatch test with context[x] => idtac end end)
      then fail 0 else idtac;
      let v := eval vm_compute in test in
      lazymatch v with
      | true => change test with true
      | false => change test with false
      end
    end]; reflexivity.
Qed.
Theorem assertions_after_reset s resetInput (reset : nreset resetInput=Zmod.one) pins n :
  asserts (run (step s resetInput) pins n) (pins n).
Proof.
  apply invariant_asserts; induction n as [|n IH].
  - exact (reset_invariant s resetInput reset).
  - apply invariant_step; exact IH.
Qed.
End MacInvariant.
Print Assumptions MacInvariant.invariant_step.

Print Assumptions MacInvariant.assertions_after_reset.
