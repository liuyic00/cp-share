From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedHistory MulDivCheckedControl.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory.
Open Scope Z_scope.
Module MulDivCheckedLatency.
Definition quiet := mkInputs 0 0 0 0 0 0 0 0 0.
Definition inputExtra s := v211 s quiet.
Definition outputExtra s := v219 s quiet.
Definition latency s := v225 s quiet.
Ltac expand_latency := unfold v225,v224,v223,v222,v221,v220,v219,v218,v217,v216,v215,
  v214,v213,v212,v211,v210,v209,v208,v207,v206,v205,v204,v203,v202,v201,v200,
  v199,v198,v197,v196,v195,v194,v193,v192,v191,v143,v43,v31.
Lemma pins_independent s i : v225 s i=latency s.
Proof. unfold latency; expand_latency; reflexivity. Qed.
Lemma extra_bounds s : 0<=inputExtra s<=1 /\ 0<=outputExtra s<=1.
Proof.
  unfold inputExtra,outputExtra,v211,v219.
  pose proof (bit_cases (Z.lor (v202 s quiet) (v210 s quiet))).
  pose proof (bit_cases (if v213 s quiet=?1 then v202 s quiet else v218 s quiet)); lia.
Qed.
Lemma division_latency s
  (operation : word 4 (r11_ncontractFn s)=4 \/ word 4 (r11_ncontractFn s)=5 \/
    word 4 (r11_ncontractFn s)=6 \/ word 4 (r11_ncontractFn s)=7) :
  latency s=65+inputExtra s+outputExtra s.
Proof.
  assert (division : v191 s quiet=1).
  { unfold v191; destruct operation as [op|[op|[op|op]]]; rewrite op; reflexivity. }
  unfold latency,v225; rewrite division; cbn [Z.eqb Pos.eqb].
  unfold v222,v212,v220,v192,v221.
  change (word 7 (word 7 (word 7 (v211 s quiet)+word 7 (v219 s quiet)+65))=65+inputExtra s+outputExtra s).
  change (word 7 (word 7 (word 7 (inputExtra s)+word 7 (outputExtra s)+65))=65+inputExtra s+outputExtra s).
  destruct (extra_bounds s) as [a b].
  assert (wa : word 7 (inputExtra s)=inputExtra s) by (apply Words.word_small; change (0<=inputExtra s<128); lia).
  assert (wb : word 7 (outputExtra s)=outputExtra s) by (apply Words.word_small; change (0<=outputExtra s<128); lia).
  rewrite normalize,wa,wb by lia.
  transitivity (inputExtra s+outputExtra s+65); [apply Words.word_small; change (0<=inputExtra s+outputExtra s+65<128); lia|lia].
Qed.
Lemma division_range s
  (operation : word 4 (r11_ncontractFn s)=4 \/ word 4 (r11_ncontractFn s)=5 \/
    word 4 (r11_ncontractFn s)=6 \/ word 4 (r11_ncontractFn s)=7) :
  65<=latency s<=67.
Proof. rewrite division_latency by exact operation; destruct (extra_bounds s); lia. Qed.
Lemma captured_congruent s t (same : captured s=captured t) :
  inputExtra s=inputExtra t /\ outputExtra s=outputExtra t /\ latency s=latency t.
Proof.
  assert (fn : word 4 (r11_ncontractFn s)=word 4 (r11_ncontractFn t))
    by exact (f_equal MulDiv.nMulDiv.nio_5Freq_5Fbits_5Ffn same).
  assert (dw : word 1 (r12_ncontractDw s)=word 1 (r12_ncontractDw t))
    by exact (f_equal MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fdw same).
  assert (a : word 64 (r13_ncontractA s)=word 64 (r13_ncontractA t))
    by exact (f_equal MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin1 same).
  assert (b : word 64 (r14_ncontractB s)=word 64 (r14_ncontractB t))
    by exact (f_equal MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin2 same).
  unfold inputExtra,outputExtra,latency; expand_latency; rewrite fn,dw,a,b; repeat split; reflexivity.
Qed.
Theorem pending_stable s i (control : MulDivCheckedControl.MulDivCheckedControl.Invariant s)
  (pending : word 1 (r9_ncontractPending s)=1) :
  inputExtra (step s i)=inputExtra s /\ outputExtra (step s i)=outputExtra s /\ latency (step s i)=latency s.
Proof. apply captured_congruent; apply MulDivCheckedControl.MulDivCheckedControl.pending_history_stable; assumption. Qed.
End MulDivCheckedLatency.
Print Assumptions MulDivCheckedLatency.division_latency.
Print Assumptions MulDivCheckedLatency.pending_stable.
