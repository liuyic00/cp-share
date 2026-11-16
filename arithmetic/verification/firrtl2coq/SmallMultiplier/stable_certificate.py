#!/usr/bin/env python3
"""Local expression certificates for the original hierarchical multiplier AST.
Child ports are explicit variables, not flattened substitute circuits.
"""
from pathlib import Path
import re,json
H=Path(__file__).resolve().parent;A=H.parents[2]
MID=globals().get('MODULE_ID',3)
PREFIX=globals().get('OUTPUT_PREFIX','')
WIDTHLOG=globals().get('WIDTH_LOG','small-widths.log')
model=(H.parent / 'Generated/ArrayMulDataModule8/Model.v').read_text()
def form(s,start):
 d=0
 for i in range(start,len(s)):
  d+=(s[i]=='(')-(s[i]==')')
  if d==0:return s[start:i+1]
 raise ValueError(start)
body=model.split(f'Definition generated_module_{MID}_stmts_0')[1].split(f'Definition generated_module_{MID} :')[0]
root_types={int(i):(int(k),int(w)) for i,k,w in re.findall(r'\(\s*(\d+)(?:%N)?,\s*\((\d+)(?:%N)?,\s*(\d+)(?:%N)?\)\)',(A/'build'/WIDTHLOG).read_text())}
ports={}
for mid in range(4):
 decl=model.split(f'Definition generated_module_{mid} :')[1].split(').',1)[0]
 ports[mid]=[(int(pid),direction,0 if kind=='Fuint' else 1 if kind=='Fsint' else 2,int(w or 1)) for direction,pid,kind,w in re.findall(r'\(@F(input|output) VarOrder.T (\d+) \(Gtyp \(?(Fuint|Fsint|Fclock)(?: (\d+))?\)?\)\)',decl)]
instances={int(i):int(m) for i,m in re.findall(r'\(@Sinst VarOrder.T (\d+) (\d+)\)',body)}
regs=set(map(int,re.findall(r'\(@Sreg VarOrder.T (\d+)',body)))
inputs={pid for pid,d,_,_ in ports[MID] if d=='input'}
key=lambda root:(0,root)
nodes={}; leaves={key(i) for i in regs|inputs}
types={key(i):t for i,t in root_types.items() if t[0]!=9}
for inst,mid in instances.items():
 for pid,d,k,w in ports[mid]:
  types[(inst,pid)]=(k,w)
  if d=='output':leaves.add((inst,pid))
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',body):
 f=form(body,m.start());nodes[key(int(m[1]))]=f[m.end()-m.start():-1]
for m in re.finditer(r'\(@Sfcnct VarOrder.T ',body):
 f=form(body,m.start());r=form(f,m.end()-m.start());rest=f[m.end()-m.start()+len(r)+1:-1]
 scalar=re.fullmatch(r'\(@Eid VarOrder.T (\d+)\)',r)
 port=re.fullmatch(r'\(@Esubfield VarOrder.T \(@Eid VarOrder.T (\d+)\) (\d+)\)',r)
 if scalar:
  n=int(scalar[1])
  if n not in regs:nodes[key(n)]=rest
 elif port:nodes[(int(port[1]),int(port[2]))]=rest
 else:raise ValueError(r)
rf=re.compile(r'\(@Eref VarOrder.T (\(@Eid VarOrder.T (\d+)\)|\(@Esubfield VarOrder.T \(@Eid VarOrder.T (\d+)\) (\d+)\))\)')
def refs(expr):
 return sorted(set((0,int(m[2])) if m[2] else (int(m[3]),int(m[4])) for m in rf.finditer(expr)))
ordered=[];done=set(leaves);active=set()
def visit(k):
 if k in done:return
 assert k not in active,k
 active.add(k)
 for d in refs(nodes[k]):visit(d)
 active.remove(k);done.add(k);ordered.append(k)
for k in nodes:visit(k)
assert done==set(types),(set(types)-done,done-set(types))
def name(k):return f'word_{k[1]}' if k[0]==0 else f'port_{k[0]}_{k[1]}'
def typ(k):
 kind,w=types[k];return 'Fclock' if kind==2 else f'({"Fuint" if kind==0 else "Fsint"} {w})'
def value(k):return f'(Gval {typ(k)} ({name(k)} v))'
def bundle(inst,fields):
 seq='Bnil'
 for pid,d,_,_ in reversed(ports[instances[inst]]):
  if pid in fields:seq=f'(Bflips {pid} {"Flipped" if d=="input" else "Nflip"} {value((inst,pid))} {seq})'
 return f'(Bval {seq})'
def env_for(deps):
 env='(VM.empty hvalue)';group={}
 for inst,pid in deps:group.setdefault(inst,[]).append(pid)
 for inst,ids in sorted(group.items()):
  if inst==0:
   for pid in ids:env=f'(VM.add {pid} {value((0,pid))} {env})'
  else:env=f'(VM.add {inst} {bundle(inst,ids)} {env})'
 return env
lines=['''(* Generated local certificates from the unchanged deep AST. *)
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model.
Local Open Scope N_scope.
Lemma refine_ground known t b : refine_boolean_result known (Some (Gval t b)) = Some (Gval t b).
Proof. destruct known; reflexivity. Qed.
Definition leaf_values := N -> N -> bits.
Definition word_of_eval (v : option hvalue) : bits := match v with Some (Gval _ b) => b | _ => [::] end.
''']
for k in sorted(leaves):lines +=[f'Definition {name(k)} (v : leaf_values) := v {k[0]} {k[1]}.']
for k in ordered:
 n=name(k);expr=nodes[k];env=env_for(refs(expr))
 lines +=[f'Definition expr_{n} : @hfexpr VarOrder.T := {expr}.',f'Definition closed_{n} (v : leaf_values) : VM.t hvalue := {env}.',f'Definition {n} (v : leaf_values) := word_of_eval (eval_hfexpr expr_{n} (closed_{n} v) (closed_{n} v)).']
lines+=['Opaque '+' '.join(name(k) for k in sorted(types))+'.']
lines+=['Definition stable_shape (values : N -> hvalue) : VM.t hvalue := Eval vm_compute in']
env='(VM.empty hvalue)'
for i in sorted(root_types):env=f'(VM.add {i} (values {i}) {env})'
lines+=[' '+env+'.','Definition stable_values (v : leaf_values) (id : N) : hvalue := match id with']
for i in sorted(root_types):
 val=bundle(i,[p for p,_,_,_ in ports[instances[i]]]) if i in instances else value((0,i))
 lines +=[f'| {i} => {val}']
lines +=['| _ => Needtobedefined (Gtyp (Fuint 0)) end.','Definition stable_env v := stable_shape (stable_values v).']
base="cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity."
for k in ordered:
 n=name(k);t=typ(k)
 lines +=[f'Transparent {n}.',f'Lemma closed_{n}_value v : eval_hfexpr expr_{n} (closed_{n} v) (closed_{n} v) = Some (Gval {t} ({n} v)).',f'Proof. unfold {n}, closed_{n}, expr_{n}, word_of_eval. {base} Qed.',f'Opaque {n}.',f'Lemma node_{n}_value v : eval_hfexpr expr_{n} (stable_env v) (stable_env v) = Some (Gval {t} ({n} v)).',f'Proof. change (eval_hfexpr expr_{n} (closed_{n} v) (closed_{n} v) = Some (Gval {t} ({n} v))). apply closed_{n}_value. Qed.']
(H/(PREFIX+'Stable.v')).write_text('\n'.join(lines)+'\n')
(H/(PREFIX+'stable-nodes.json')).write_text(json.dumps({'root_types':root_types,'ports':ports,'instances':instances,'registers':sorted(regs),'inputs':sorted(inputs),'order':ordered},indent=2)+'\n')
print(len(ordered),'scalar/port nodes;',len(leaves),'leaf vectors')
