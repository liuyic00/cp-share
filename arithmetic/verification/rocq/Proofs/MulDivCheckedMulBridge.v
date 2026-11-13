From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedMulSpec MulDivCheckedProductBits MulDivCheckedData.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked MulDivCheckedHistory.MulDivCheckedHistory
  MulDivCheckedProductBits.MulDivCheckedProductBits MulDivCheckedData.MulDivCheckedData.
Open Scope Z_scope.
Module MulDivCheckedMulBridge.
Module M := MulDivCheckedMulSpec.MulDivCheckedMulSpec.
Lemma extend_mux x b (bit : b=0 \/ b=1) :
  word 128 (Z.shiftl (word 64 (repeatWord 64 1 (word 1 (Z.land b (word 1 (Z.shiftr (word 64 x) 63)))))) 64+word 64 x)=
  word 128 (if b=?1 then SignedWords.signed 64 x else word 64 x).
Proof.
  destruct bit as [bit|bit]; subst b.
  - rewrite Z.land_0_l; change (word 64 (repeatWord 64 1 (word 1 0))) with 0.
    rewrite Z.shiftl_0_l,Z.add_0_l; reflexivity.
  - assert (one : word 1 (Z.land 1 (word 1 (Z.shiftr (word 64 x) 63)))=word 1 (Z.shiftr (word 64 x) 63)).
    { destruct (bit_cases (Z.shiftr (word 64 x) 63)) as [h|h]; rewrite h; reflexivity. }
    rewrite one; change (1=?1) with true; apply sign_extend.
Qed.
Lemma product_operands s i : v254 s i=word 128
  ((if v245 s i=?1 then SignedWords.signed 64 (r13_ncontractA s) else word 64 (r13_ncontractA s))*
   (if v242 s i=?1 then SignedWords.signed 64 (r14_ncontractB s) else word 64 (r14_ncontractB s))).
Proof.
  unfold v254,v249,v253,v248,v252,v247,v251,v246,v250.
  rewrite !extend_mux by (unfold v245,v242; apply bit_cases).
  apply product_mod.
Qed.
Lemma product_unsigned s i (op : word 4 (r11_ncontractFn s)=0 \/ word 4 (r11_ncontractFn s)=3) :
  v254 s i=word 128 (word 64 (r13_ncontractA s)*word 64 (r14_ncontractB s)).
Proof.
  rewrite product_operands; unfold v245,v244,v243,v242,v241; destruct op as [fn|fn]; rewrite fn; reflexivity.
Qed.
Lemma product_signed s i (op : word 4 (r11_ncontractFn s)=1) :
  v254 s i=word 128 (SignedWords.signed 64 (r13_ncontractA s)*SignedWords.signed 64 (r14_ncontractB s)).
Proof. rewrite product_operands; unfold v245,v244,v243,v242,v241; rewrite op; reflexivity. Qed.
Lemma product_mixed s i (op : word 4 (r11_ncontractFn s)=2) :
  v254 s i=word 128 (SignedWords.signed 64 (r13_ncontractA s)*word 64 (r14_ncontractB s)).
Proof. rewrite product_operands; unfold v245,v244,v243,v242,v241; rewrite op; reflexivity. Qed.
Lemma multiply_expected s i (op : word 4 (r11_ncontractFn s)<4) : v263 s i=format (r12_ncontractDw s) (v257 s i).
Proof.
  assert (division : v191 s i=0).
  { pose proof (bounds 4 (r11_ncontractFn s) ltac:(lia)) as bound.
    assert (cases : word 4 (r11_ncontractFn s)=0 \/ word 4 (r11_ncontractFn s)=1 \/ word 4 (r11_ncontractFn s)=2 \/ word 4 (r11_ncontractFn s)=3) by lia.
    unfold v191; destruct cases as [fn|[fn|[fn|fn]]]; rewrite fn; reflexivity. }
  rewrite expected_format; unfold v258; rewrite division; cbn [Z.eqb]; apply format_normal.
Qed.
Lemma low_expected s i (op : word 4 (r11_ncontractFn s)=0) :
  v263 s i=format (r12_ncontractDw s) (word 64 (r13_ncontractA s)*word 64 (r14_ncontractB s)).
Proof.
  rewrite multiply_expected by lia; unfold v257,v240,v154; rewrite op.
  change (format (r12_ncontractDw s) (word 64 (v255 s i))=format (r12_ncontractDw s) (word 64 (r13_ncontractA s)*word 64 (r14_ncontractB s))).
  rewrite format_normal; unfold v255; rewrite (product_unsigned s i (or_introl op)),Z.shiftr_0_r,low; apply format_normal.
Qed.
Lemma high_expected s i (op : word 4 (r11_ncontractFn s)<4)
  (nonzero : word 4 (r11_ncontractFn s)<>0) (full : word 1 (r12_ncontractDw s)=1) :
  v263 s i=word 64 (Z.shiftr (v254 s i) 64).
Proof.
  rewrite multiply_expected by exact op; unfold format; rewrite full; cbn [Z.eqb Pos.eqb].
  unfold v257,v240,v154; change (word 4 0) with 0.
  assert (off : (word 4 (r11_ncontractFn s)=?0)=false) by (apply Z.eqb_neq; exact nonzero).
  rewrite off; change (word 64 (word 64 (v256 s i))=word 64 (Z.shiftr (v254 s i) 64)).
  unfold v256; repeat rewrite normalize by lia; reflexivity.
Qed.
Definition rawRequest s := MulDiv.nMulDiv.mkInputs 0 1 (r11_ncontractFn s) (r12_ncontractDw s)
  (r13_ncontractA s) (r14_ncontractB s) (r15_ncontractTag s) 0 0.
Lemma specification_raw s : M.specification (captured s)=M.specification (rawRequest s).
Proof.
  apply M.specification_congruent;
    cbn [captured rawRequest MulDiv.nMulDiv.nio_5Freq_5Fbits_5Ffn MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fdw MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin1 MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin2];
    apply Words.word_idem; lia.
Qed.
Lemma word_format a b : word 64 (SignedWords.signed 32 (word 64 a*word 64 b))=
  word 64 (SignedWords.signed 32 (word 32 (SignedWords.signed 32 b*word 32 a))).
Proof.
  assert (normal : SignedWords.signed 32 (word 64 a*word 64 b)=SignedWords.signed 32 (word 32 (word 64 a*word 64 b))).
  { symmetry; apply SignedWords.signed_normal; lia. }
  rewrite normal,product_word; reflexivity.
Qed.
Theorem expected_eq_specification s i
  (legal : word 4 (r11_ncontractFn s)<4 /\ (word 4 (r11_ncontractFn s)=0 \/ word 1 (r12_ncontractDw s)=1)) :
  v263 s i=M.specification (captured s).
Proof.
  destruct legal as [range width]; pose proof (bounds 4 (r11_ncontractFn s) ltac:(lia)) as bound.
  assert (cases : word 4 (r11_ncontractFn s)=0 \/ word 4 (r11_ncontractFn s)=1 \/
    word 4 (r11_ncontractFn s)=2 \/ word 4 (r11_ncontractFn s)=3) by lia.
  assert (bridge : MulDiv.CIRCTBits.word=word) by reflexivity.
  rewrite specification_raw.
  unfold M.specification,M.L.specification,M.W.specification,M.U.specification,M.S.specification,
    MulDivMulSignedCapture.MulDivMulSignedCapture.multiplicand,rawRequest.
  cbn [MulDiv.nMulDiv.nio_5Freq_5Fbits_5Ffn MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fdw MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin1 MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin2].
  rewrite bridge.
  destruct cases as [fn|[fn|[fn|fn]]]; rewrite fn; cbn [Z.eqb Pos.eqb].
  - rewrite (low_expected s i fn); unfold format.
    destruct (word 1 (r12_ncontractDw s)=?1); [reflexivity|apply word_format].
  - rewrite high_expected by lia; rewrite (product_signed s i fn); apply high.
  - rewrite high_expected by lia; rewrite (product_mixed s i fn); apply high.
  - rewrite high_expected by lia; rewrite (product_unsigned s i (or_intror fn)); apply high.
Qed.
End MulDivCheckedMulBridge.
Print Assumptions MulDivCheckedMulBridge.expected_eq_specification.
Print Assumptions MulDivCheckedMulBridge.product_operands.
