#!/usr/bin/env python3
"""Generate local certificates from the unchanged firrtl2coq divider AST."""
from pathlib import Path
import re, json, argparse, tempfile, subprocess
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
REPO=ROOT.parent
TOOL=REPO/'tool/firrtl2coq'
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--model',type=Path,help='Reuse an existing unmodified firrtl2coq output')
p.add_argument('--widths-log',type=Path,help='Reuse a width diagnostic while developing the generator')
p.add_argument('--coq-switch',default='firrtl2coq')
a=p.parse_args()
(ROOT/'build').mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='divider-certificates-',dir=ROOT/'build') as tmp:
 temp=Path(tmp)
 if a.model:
  raw=a.model.read_text()
 else:
  subprocess.run([str(TOOL/'src/ocaml/_build/default/bin/main.exe'),
    str(ROOT/'artifacts/chisel3/firrtl/Radix2Divider.lo.fir'),str(temp/'Raw.v')],check=True)
  raw=(temp/'Raw.v').read_text()
 model=raw.split('(* Generated verification properties. *)')[0]
 if 'Definition generated_top := 0.' not in model:
  raise SystemExit('Unexpected divider top; review generator schema')
 (HERE/'Model.v').write_text(model)
 if a.widths_log:
  width_text=a.widths_log.read_text()
 else:
  (temp/'Widths.v').write_text(model+"""
Definition all_widths := match module_initial_map_with_memory generated_modules [::] generated_top None (Semantics_with_implicit_widths.SVM.empty (VM.t Semantics_with_implicit_widths.hvalue)) with
| Some sts => match Semantics_with_implicit_widths.SVM.find [::] sts with
| Some env => map (fun kv => (fst kv, match Semantics_with_implicit_widths.type_of_val (snd kv) with | Gtyp (Fuint w) => N.of_nat w | Gtyp Fclock => 1 | _ => 0 end)) (VM.elements env)
| _ => [::] end | _ => [::] end.
Set Printing Width 1000000.
Eval vm_compute in all_widths.
""")
  command=['opam','exec','--switch='+a.coq_switch,'--','coqc',
   '-Q',str(TOOL/'lib/simplssrlib'),'simplssrlib',
   '-Q',str(TOOL/'lib/nbits'),'nbits','-R',str(TOOL/'src'),'firrtl',str(temp/'Widths.v')]
  width_text=subprocess.check_output(command,text=True)
width_text=width_text.split('     = [::',1)[1]
widths={int(a):int(b) for a,b in re.findall(r'\((\d+), (\d+)\)',width_text)}
def take_form(text,start):
 depth=0
 for i in range(start,len(text)):
  depth+=(text[i]=='(')-(text[i]==')')
  if depth==0:return text[start:i+1]
 raise ValueError(start)
nodes={}
for match in re.finditer(r'\(@Snode VarOrder.T (\d+) ',model):
 full=take_form(model,match.start()); nodes[int(match[1])]=full[full.index(' ',full.index(match[1]))+1:-1]
regs=set(map(int,re.findall(r'\(@Sreg VarOrder.T (\d+)',model)))
inputs=set(map(int,re.findall(r'\(@Finput VarOrder.T (\d+)',model)))
for match in re.finditer(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T (\d+)\) ',model):
 id=int(match[1]);full=take_form(model,match.start()); expr=full[match.end()-match.start():-1]
 if id not in regs:nodes[id]=expr
ref=re.compile(r'\(@Eref VarOrder.T \(@Eid VarOrder.T (\d+)\)\)')
leaf=regs|inputs
ordered=[];active=set();done=set(leaf)
def visit(id):
 if id in done:return
 assert id not in active, id
 active.add(id)
 for dep in ref.findall(nodes[id]):visit(int(dep))
 active.remove(id);done.add(id);ordered.append(id)
for id in nodes:visit(id)
lines=['''(* Generated from the original deep-embedded AST.  No proof assumptions. *)
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
  HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From Divider Require Import Model.
Local Open Scope N_scope.
Lemma refine_ground known t b : refine_boolean_result known (Some (Gval t b)) = Some (Gval t b).
Proof. destruct known; reflexivity. Qed.
Fixpoint find_driver (id : N) (stmts : @hfstmt_seq VarOrder.T) : option (@hfexpr VarOrder.T) :=
 match stmts with
 | Qnil => None
 | Qcons (Snode n e) tail => if id == n then Some e else find_driver id tail
 | Qcons (Sfcnct (Eid n) e) tail => if id == n then Some e else find_driver id tail
 | Qcons _ tail => find_driver id tail
 end.
Definition leaf_values := N -> bits.
Definition word_of_eval (v : option hvalue) : bits :=
 match v with Some (Gval _ b) => b | _ => [::] end.
''']
for id in sorted(leaf): lines += [f'Definition word_{id} (v : leaf_values) := v {id}.']
for id in ordered:
 expr=nodes[id]
 deps=sorted(set(map(int,ref.findall(expr))))
 env='(VM.empty hvalue)'
 for dep in deps: env=f'(VM.add {dep} (Gval (Fuint {widths[dep]}) (word_{dep} v)) {env})'
 lines += [f'Definition expr_{id} : @hfexpr VarOrder.T := {expr}.',
 f'Definition closed_{id} (v : leaf_values) : VM.t hvalue := {env}.',
 f'Definition word_{id} (v : leaf_values) := word_of_eval (eval_hfexpr expr_{id} (closed_{id} v) (closed_{id} v)).']
lines += ['Opaque '+' '.join(f'word_{id}' for id in sorted(widths))+'.']
lines+=['Definition stable_shape (values : N -> hvalue) : VM.t hvalue := Eval vm_compute in']
env='(VM.empty hvalue)'
for id in sorted(widths): env=f'(VM.add {id} (values {id}) {env})'
lines += ['  '+env+'.']
lines += ['Definition stable_values (v : leaf_values) (id : N) : hvalue := match id with']
for id in sorted(widths):
 ty='Fclock' if id==0 else f'(Fuint {widths[id]})'
 lines += [f'| {id} => Gval {ty} (word_{id} v)']
lines += ['| _ => Needtobedefined (Gtyp (Fuint 0)) end.', 'Definition stable_env v := stable_shape (stable_values v).']
lines += ['Opaque '+' '.join(f'word_{id}' for id in sorted(widths))+'.']
for id in ordered:
 lines += [f'Lemma source_{id} : find_driver {id} generated_module_0_stmts_0 = Some expr_{id}.', 'Proof. vm_compute. reflexivity. Qed.', f'Transparent word_{id}.', f'Lemma closed_{id}_value v : eval_hfexpr expr_{id} (closed_{id} v) (closed_{id} v) = Some (Gval (Fuint {widths[id]}) (word_{id} v)).',
 f"Proof. unfold word_{id}, closed_{id}, expr_{id}, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr\' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.",
 f'Opaque word_{id}.', f'Lemma node_{id}_value v : eval_hfexpr expr_{id} (stable_env v) (stable_env v) = Some (Gval (Fuint {widths[id]}) (word_{id} v)).',
 f'Proof. change (eval_hfexpr expr_{id} (closed_{id} v) (closed_{id} v) = Some (Gval (Fuint {widths[id]}) (word_{id} v))). apply closed_{id}_value. Qed.']
lines += ['Print Assumptions node_14_value.', 'Print Assumptions node_483_value.']
(HERE/'Stable.v').write_text('\n'.join(lines)+'\n')
(HERE/'nodes.json').write_text(json.dumps({'widths':widths,'registers':sorted(regs),'inputs':sorted(inputs),'order':ordered,'expressions':nodes},indent=2)+'\n')
print(len(nodes),'nodes; first:',ordered[:40])
