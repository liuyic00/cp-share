from pathlib import Path
import re,json
P=Path(__file__).resolve().parent
j=json.loads((P/'nodes.json').read_text()); regs=j['registers'];width={int(k):v for k,v in j['widths'].items()}
c=(P/'Commit.v').read_text()
s=['''From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts NormalizationFacts.
From Divider Require Import Stable Representation Typing Muxes MuxShapes LeafWords Controls ReferenceNormalization Commit StateNext DataNext CountNext OutputLink RuntimeRepresentation.
Local Open Scope Z_scope.
Lemma adapted_word_size width bits : size (zext_to width (take width bits)) = width.
Proof. rewrite /zext_to size_zext. apply subnKC. rewrite size_take. apply geq_minl. Qed.
''']
refs={}
for id in regs:
 e=re.search(r'Definition next_expr_'+str(id)+r'.*? := (.*)\.',c)[1];refs[id]=list(map(int,re.findall(r'Eid VarOrder.T (\d+)',e)))
 s.append(f'''Lemma next_{id}_size v : size (next_word_{id} v) = {width[id]}%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_{id}.
Lemma next_{id}_clock v clock : next_word_{id} (with_clock v clock) = next_word_{id} v.
Proof. unfold next_word_{id}, next_raw_word_{id}, next_closed_{id}. rewrite {' '.join('word_'+str(x)+'_clock' for x in refs[id])}. reflexivity. Qed.
Opaque next_raw_word_{id}.
''')
mp={18:(19,24,'r1_ndivBy0Reg'),33:(34,47,'r3_naSignReg'),38:(39,52,'r4_nqSignReg'),40:(41,55,'r5_nbReg'),43:(44,59,'r6_naValx2Reg'),46:(49,60,'r7_nctrlReg_5FisW'),47:(48,61,'r8_nctrlReg_5FisHi'),476:(9,412,'r14_npreviousOutput')}
for id,(src,ref,field) in mp.items():
 eq=f'control_{src}_reference' if src!=9 else 'output_9_reference'
 s.append(f'''Transparent next_raw_word_{id}.
Lemma next_{id}_raw v : next_raw_word_{id} v = word_{src} v.
Proof. unfold next_raw_word_{id}, next_closed_{id}, next_expr_{id}, word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque next_raw_word_{id}.
Lemma next_{id}_reference s i ghost : to_Zpos (next_word_{id} (encoded_leaves s i ghost)) = Reference.{field} (Reference.step s i).
Proof. unfold next_word_{id}. rewrite unsigned_adapt next_{id}_raw {eq} reference_{ref}_normalized. reflexivity. Qed.
''')
for id,src,field in [(446,13,'r11_npreviousState'),(447,51,'r12_npreviousCount')]:
 s.append(f'''Transparent next_raw_word_{id}.
Lemma next_{id}_raw v : next_raw_word_{id} v = word_{src} v.
Proof. unfold next_raw_word_{id}, next_closed_{id}, next_expr_{id}, word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque next_raw_word_{id}.
Lemma next_{id}_reference s i ghost : to_Zpos (next_word_{id} (encoded_leaves s i ghost)) = Reference.{field} (Reference.step s i).
Proof. unfold next_word_{id}. rewrite unsigned_adapt next_{id}_raw leaf_{src}_integer normalize_nested; [reflexivity|lia]. Qed.
''')
(P/'NextState.v').write_text(''.join(s))
