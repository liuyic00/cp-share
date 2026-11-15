from pathlib import Path
import json,re
H=Path(__file__).resolve().parent
g=json.loads((H/'global-dependencies.json').read_text());idx=json.loads((H/'global-key-index.json').read_text())
header='''From Coq Require Import ZArith NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalChildren Child0Stable Child1Stable Child2Stable ChildAbstract Compressors.
Local Open Scope N_scope.
'''
alias={}
s=header
for k in g['order']:
 node=g['nodes'][k];n=idx[k]
 if node['kind'].startswith('sync'):
  alias[k]=node['deps'][0]
  s+=f'Lemma wire_alias_{n} v : global_word_{n} v = global_word_{idx[alias[k]]} v. Proof. apply global_sync_{n}. Qed.\n'
 elif node['expr'].startswith('(@Eref '):
  assert len(node['deps'])==1;alias[k]=node['deps'][0];dn=idx[alias[k]]
  # Recover the exact ground type from the existing checked theorem.
  src=(H/'GlobalStable.v').read_text() if 'src' not in globals() else src
  ty=re.search(rf'Lemma global_closed_{n}_value v :.*?Some \(Gval (.*?) \(global_word_{n} v\)\)',src)[1]
  s+=f'''Lemma wire_alias_{n} v : global_word_{n} v = global_word_{dn} v.
Proof. have E := global_closed_{n}_value v.
 change (Some (Gval {ty} (global_word_{dn} v)) = Some (Gval {ty} (global_word_{n} v))) in E.
 exact (Logic.eq_sym (f_equal Stable.word_of_eval E)). Qed.
'''
(H/'GlobalAliases.v').write_text(s)
# Same enumeration used by global_child_certificate.py / GlobalChildren.v.
instances=list(g['instances'].items());nums={p:n for n,(p,_) in enumerate(instances)}
def pathkey(p,id):return p+':'+str(id)
def aliases_to(k,stops):
 found=[]
 while k not in stops and k in alias:
  found.append(f'wire_alias_{idx[k]}');k=alias[k]
 return k,found
s=header+'From SmallMultiplier Require Import GlobalAliases.\n'
for p,mid in sorted(instances,key=lambda x:-x[0].count('/')):
 if mid==3:continue
 num=nums[p];args=['a','b','c','d','e'][:[2,3,5][mid]];outs=[[4,5],[5,6],[7,8,9]][mid];pred=[15,19,34][mid]
 exprs=[['xorb a b','andb a b'],['fa_sum a b c','fa_carry a b c'],['fa_sum (fa_sum a b c) d e','fa_carry a b c','fa_carry (fa_sum a b c) d e']][mid]
 s+=f'Lemma instance_{num}_bits v ({" ".join(args)}:bool)\n'
 for j,a in enumerate(args):s+=f' (E{j+2}:global_word_{idx[pathkey(p,j+2)]} v=[::{a}])\n'
 claims=[(pathkey(p,o),e) for o,e in zip(outs,exprs)]+[(pathkey(p,pred),'true')]
 s+=' : '+' /\\ '.join(f'global_word_{idx[k]} v=[::{e}]' for k,e in claims)+'.\nProof.\n'
 stops={pathkey(p,j+2):f'E{j+2}' for j in range(len(args))}
 if mid==2:
  for child,childargs in [(10,['a','b','c']),(11,['(fa_sum a b c)','d','e'])]:
   cp=p+'/'+str(child);cn=nums[cp]
   s+=f' have C{child}: global_word_{idx[pathkey(cp,5)]} v=[::fa_sum {" ".join(childargs)}] /\\ global_word_{idx[pathkey(cp,6)]} v=[::fa_carry {" ".join(childargs)}] /\\ global_word_{idx[pathkey(cp,19)]} v=[::true].\n'
   s+=f' {{ apply instance_{cn}_bits.\n'
   for j in range(3):
    end,chain=aliases_to(pathkey(cp,j+2),set(stops))
    assert end in stops,(p,cp,end)
    s+='   - '+('rewrite '+' '.join(chain)+'. ' if chain else '')+'exact '+stops[end]+'.\n'
   s+=' }\n'
   s+=f' destruct C{child} as [S{child} [C{child} A{child}]].\n'
   stops[pathkey(cp,5)]=f'S{child}';stops[pathkey(cp,6)]=f'C{child}'
 s+=' repeat split.\n'
 for out,expr in [*zip(outs,exprs),(pred,'true')]:
  s+=f' - rewrite -instance_{num}_word_{out}.\n'
  s+=f'   apply (abstract_child{mid}_{out} _ {" ".join(args)}).\n'
  deps=re.search(rf'Lemma word_{out}_inputs v w (.*?) : word_', (H/f'Child{mid}Congruence.v').read_text())[1]
  for scope,id in [tuple(map(int,x)) for x in re.findall(r'v (\d+) (\d+)',deps)]:
   key=pathkey(p,id) if scope==0 else p+':'+str(scope)+':'+str(id)
   end,chain=aliases_to(key,set(stops));assert end in stops,(p,out,key,end)
   s+=f'   + change (global_word_{idx[key]} v = [::{dict((x[0],x[1]) for x in [])}]).\n' if False else ''
   s+=f'   + cbn [instance_{num}_leaves]. '+('rewrite '+' '.join(chain)+'. ' if chain else '')+'exact '+stops[end]+'.\n'
 s+='Qed.\n'
(H/'GlobalChildBits.v').write_text(s)
