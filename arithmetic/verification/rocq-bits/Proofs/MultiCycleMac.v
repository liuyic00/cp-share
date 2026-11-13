From Stdlib Require Import ZArith Lia Zmod.Bits.
From BitsGenerated Require Import MultiCycleMac.
Import MultiCycleMac.nMultiCycleMac.
Open Scope Z_scope.
Module MultiCycleMacProofs.
Definition sum8 (a b : bits 8) : bits 9 :=
  Zmod.add (Zmod.app a (bits.of_Z 1 0)) (Zmod.app b (bits.of_Z 1 0)).
Definition product (sum : bits 9) (c : bits 8) : bits 17 :=
  Zmod.mul (Zmod.app sum (bits.of_Z 8 0)) (Zmod.app c (bits.of_Z 9 0)).
Definition arithmetic (a b c : bits 8) := product (sum8 a b) c.
Ltac expand := unfold v46, v45, v44, v43, v42, v41, v40, v39, v38, v37, v36, v35, v34, v33, v32, v31, v30, v29, v28, v27, v26, v25, v24, v23, v22, v21, v20, v19, v18, v17, v16, v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0.
Theorem reset_idle s i (reset : nreset i=Zmod.one) : r0_nstate (step s i)=bits.of_Z 2 0.
Proof. unfold step; cbn [r0_nstate]; rewrite reset; reflexivity. Qed.
Lemma capture s i (idle : r0_nstate s=bits.of_Z 2 0)
  (reset : nreset i=Zmod.zero) (valid : nio_5Fin_5Fvalid i=Zmod.one) :
  r0_nstate (step s i)=bits.of_Z 2 1 /\
  r1_noperands_5Fa (step s i)=nio_5Fin_5Fbits_5Fa i /\
  r2_noperands_5Fb (step s i)=nio_5Fin_5Fbits_5Fb i /\
  r3_noperands_5Fc (step s i)=nio_5Fin_5Fbits_5Fc i.
Proof.
  unfold step; cbn [r0_nstate r1_noperands_5Fa r2_noperands_5Fb r3_noperands_5Fc].
  expand; rewrite idle,reset,valid; repeat split; reflexivity.
Qed.
Lemma adding s i (state : r0_nstate s=bits.of_Z 2 1) (reset : nreset i=Zmod.zero) :
  r0_nstate (step s i)=bits.of_Z 2 2 /\
  r3_noperands_5Fc (step s i)=r3_noperands_5Fc s /\
  r4_nsum (step s i)=sum8 (r1_noperands_5Fa s) (r2_noperands_5Fb s).
Proof.
  unfold step; cbn [r0_nstate r3_noperands_5Fc r4_nsum].
  expand; rewrite state,reset; repeat split; reflexivity.
Qed.
Lemma multiplying s i (state : r0_nstate s=bits.of_Z 2 2) (reset : nreset i=Zmod.zero) :
  r0_nstate (step s i)=bits.of_Z 2 3 /\
  r5_nresult (step s i)=product (r4_nsum s) (r3_noperands_5Fc s).
Proof.
  unfold step; cbn [r0_nstate r5_nresult].
  expand; rewrite state,reset; split; reflexivity.
Qed.
Lemma output s i (state : r0_nstate s=bits.of_Z 2 3) (reset : nreset i=Zmod.zero) :
  nio_5Fout_5Fvalid (observe s i)=Zmod.one /\ nio_5Fout_5Fbits (observe s i)=r5_nresult s.
Proof. unfold observe; cbn [nio_5Fout_5Fvalid nio_5Fout_5Fbits]; expand; rewrite state,reset; split; reflexivity. Qed.
Theorem completes_after_two s accept add multiply later
  (idle : r0_nstate s=bits.of_Z 2 0)
  (r0 : nreset accept=Zmod.zero) (valid : nio_5Fin_5Fvalid accept=Zmod.one)
  (r1 : nreset add=Zmod.zero) (r2 : nreset multiply=Zmod.zero) (r3 : nreset later=Zmod.zero) :
  let final := observe (step (step (step s accept) add) multiply) later in
  nio_5Fout_5Fvalid final=Zmod.one /\
  nio_5Fout_5Fbits final=arithmetic (nio_5Fin_5Fbits_5Fa accept) (nio_5Fin_5Fbits_5Fb accept) (nio_5Fin_5Fbits_5Fc accept).
Proof.
  destruct (capture s accept idle r0 valid) as [st [a [b c]]].
  destruct (adding _ add st r1) as [st2 [c2 sum]].
  destruct (multiplying _ multiply st2 r2) as [st3 result].
  destruct (output _ later st3 r3) as [hv data].
  cbn zeta; split; [exact hv|].
  rewrite data,result,sum,c2,a,b,c; reflexivity.
Qed.
Theorem no_early_output s accept add multiply
  (idle : r0_nstate s=bits.of_Z 2 0)
  (r0 : nreset accept=Zmod.zero) (valid : nio_5Fin_5Fvalid accept=Zmod.one)
  (r1 : nreset add=Zmod.zero) (r2 : nreset multiply=Zmod.zero) :
  nio_5Fout_5Fvalid (observe (step s accept) add)=Zmod.zero /\
  nio_5Fout_5Fvalid (observe (step (step s accept) add) multiply)=Zmod.zero.
Proof.
  destruct (capture s accept idle r0 valid) as [st rest].
  destruct (adding _ add st r1) as [st2 rest2].
  unfold observe; cbn [nio_5Fout_5Fvalid]; unfold v11,v10,v9,v8,v6.
  rewrite st,st2,r1,r2; split; reflexivity.
Qed.
Theorem stall_stable s i later
  (done : r0_nstate s=bits.of_Z 2 3)
  (reset : nreset i=Zmod.zero) (laterReset : nreset later=Zmod.zero)
  (ready : nio_5Fout_5Fready i=Zmod.zero) :
  nio_5Fout_5Fvalid (observe (step s i) later)=Zmod.one /\
  nio_5Fout_5Fbits (observe (step s i) later)=nio_5Fout_5Fbits (observe s i).
Proof.
  assert (kept : r0_nstate (step s i)=bits.of_Z 2 3 /\ r5_nresult (step s i)=r5_nresult s).
  { unfold step; cbn [r0_nstate r5_nresult]; expand; rewrite done,reset,ready; split; reflexivity. }
  destruct kept as [state result].
  destruct (output _ later state laterReset) as [hv data].
  destruct (output s i done reset) as [_ previous].
  split; [exact hv|rewrite data,result,previous; reflexivity].
Qed.
Lemma unsigned_extend n m (x : bits n) (hn : 0<=n) (hm : 0<=m) :
  Zmod.unsigned (Zmod.app x (@Zmod.zero (2^m)))=Zmod.unsigned x.
Proof.
  rewrite bits.unsigned_app by lia.
  rewrite Zmod.unsigned_0,Z.shiftl_0_l,Z.lor_0_r; reflexivity.
Qed.
Theorem arithmetic_to_Z (a b c : bits 8) :
  Zmod.unsigned (arithmetic a b c)=
    (Zmod.unsigned a+Zmod.unsigned b)*Zmod.unsigned c.
Proof.
  pose proof (bits.unsigned_range a ltac:(lia)) as ha.
  pose proof (bits.unsigned_range b ltac:(lia)) as hb.
  pose proof (bits.unsigned_range c ltac:(lia)) as hc.
  change (0<=Zmod.unsigned a<256) in ha.
  change (0<=Zmod.unsigned b<256) in hb.
  change (0<=Zmod.unsigned c<256) in hc.
  unfold arithmetic,product,sum8.
  rewrite bits.unsigned_mul.
  rewrite !unsigned_extend by lia.
  rewrite bits.unsigned_add.
  rewrite !unsigned_extend by lia.
  replace (@Zmod.unsigned (2^(9+8)) (@Zmod.app 8 9 c (bits.of_Z 9 0)))
    with (Zmod.unsigned c).
  2: { symmetry; exact (unsigned_extend 8 9 c ltac:(lia) ltac:(lia)). }
  change (((Zmod.unsigned a+Zmod.unsigned b) mod 512 * Zmod.unsigned c) mod 131072=
    (Zmod.unsigned a+Zmod.unsigned b)*Zmod.unsigned c).
  rewrite (Z.mod_small (Zmod.unsigned a+Zmod.unsigned b) 512) by lia.
  apply Z.mod_small; nia.
Qed.
End MultiCycleMacProofs.
Print Assumptions MultiCycleMacProofs.completes_after_two.
Print Assumptions MultiCycleMacProofs.no_early_output.
Print Assumptions MultiCycleMacProofs.stall_stable.
Print Assumptions MultiCycleMacProofs.arithmetic_to_Z.
