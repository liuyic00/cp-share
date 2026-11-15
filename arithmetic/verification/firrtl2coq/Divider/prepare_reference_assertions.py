#!/usr/bin/env python3
from pathlib import Path
import re
P=Path(__file__).resolve().parent;raw=(P.parent/'Generated/Radix2Divider.v').read_text()
guards=[[(8,1),(18,1),(423,1)],[(8,1),(18,1),(428,1)],[(8,1),(18,0),(432,1)],[(8,1),(18,0),(439,1)],[(8,1),(18,0),(443,1)],[(445,1),(448,1),(451,1)],[(445,1),(453,1),(456,1)],[(445,1),(458,1),(463,1)],[(445,1),(458,1),(471,1)],[(475,1),(478,1)],[(475,1),(482,1)]]
guardids=[416,416,421,421,421,433,435,440,440,444,444];predids=[414,418,419,430,431,6,8,438,443,399,445]
leaf={18:'r1_ndivBy0Reg',445:'r10_nhistoryValid',475:'r13_nwasStalled'}
s=['''From Coq Require Import ZArith List Bool.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths.
From Divider Require Import Stable Representation LeafWords Controls OutputLink AssertTransfer AssertBooleans.
Module OldBits := Generated.Radix2Divider.CIRCTBits.
Local Open Scope Z_scope.
''']
for id,conds in enumerate(guards):
 m=re.search(r'Definition generated_assert_m0_'+str(id)+r'_local .*? := generated_expr_true (.*?) sem -> generated_expr_true (.*?) sem\.',raw);g,p=m.groups();g=re.sub(r'VarOrder.T (\d+)',r'VarOrder.T (N.of_nat (\1%nat))',g);pid=int(re.search(r'Eid VarOrder.T (\d+)',p)[1]);rg,rp=guardids[id],predids[id]
 s.append(f'''Lemma reference_check_{id} s i (checks : Reference.asserts s i)
 (enabled : Reference.v{rg} s i = 1) : Reference.v{rp} s i = 1.
Proof.
 unfold Reference.asserts in checks.
 have allchecks := (proj1 (@List.forallb_forall bool (fun b => b) (Reference.assertionChecks s i))) checks.
 have member : List.In (orb (negb (Z.eqb (Reference.v{rg} s i) 1)) (Z.eqb (Reference.v{rp} s i) 1)) (Reference.assertionChecks s i).
 {{ unfold Reference.assertionChecks. ''')
 s.append(('do '+str(id)+' right. ' if id else '')+'left; reflexivity. }\n')
 s.append(f''' have valid := allchecks _ member. rewrite enabled Z.eqb_refl in valid.
 cbn [negb orb] in valid. apply Z.eqb_eq. exact valid.
Qed.
Lemma assertion_{id}_guard_reference s i ghost
 (enabled : Tool.generated_expr_true {g} (stable_env (encoded_leaves s i ghost))) :
 Reference.v{rg} s i = 1.
Proof.
 apply (proj1 (assertion_{id}_guard_integers s i ghost)) in enabled.
''')
 pat=''
 for n,(dep,val) in enumerate(conds):pat+=f'[H{dep} ' if n<len(conds)-1 else f'H{dep}'
 pat+=']'*(len(conds)-1);s.append(f' destruct enabled as {pat}.\n')
 for dep,val in conds:
  if dep in leaf:
   s.append(f' rewrite leaf_{dep}_integer in H{dep}. change (OldBits.word 1 (Reference.{leaf[dep]} s) = {val}) in H{dep}.\n')
  else:
   s.append(f' rewrite control_{dep}_reference in H{dep}.\n')
   if dep==8:s.append(' change (Reference.v399 s i = 1) in H8.\n')
 extra=', Reference.v420, Reference.v22' if id in [2,3,4] else ''
 s.append(f' unfold Reference.v{rg}{extra}. rewrite '+ ' '.join('H'+str(dep) for dep,val in conds)+'. reflexivity.\nQed.\n')
 s.append(f'''Lemma reference_assertion_{id} s i ghost
 (checks : Reference.asserts s i) : Tool.generated_assert_m0_{id}_local (stable_env (encoded_leaves s i ghost)).
Proof.
 unfold Tool.generated_assert_m0_{id}_local. intro enabled.
 apply (proj2 (assertion_{id}_predicate_integer s i ghost)).
''')
 s.append(f' rewrite '+('output_480_reference' if id==10 else f'control_{pid}_reference')+'.\n')
 if id==9:s.append(' change (Reference.v399 s i = 1).\n')
 s.append(f' apply reference_check_{id}; [exact checks|]. exact (assertion_{id}_guard_reference s i ghost enabled).\nQed.\n')
s.append('Print Assumptions reference_assertion_10.\n')
(P/'ReferenceAssertions.v').write_text(''.join(s))
