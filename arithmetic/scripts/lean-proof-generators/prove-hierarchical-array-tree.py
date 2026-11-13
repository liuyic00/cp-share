#!/usr/bin/env python3
"""Recover weighted compressor connections from the hierarchical Lean model."""
from pathlib import Path
from collections import defaultdict, deque
import json
import re

root = Path(__file__).resolve().parents[2] / 'verification'
parts = root/'lean-hierarchical/Generated/ArrayMulDataModule'
text = '\n'.join(p.read_text() for p in sorted(parts.glob('Part*.lean')))
text = text[text.index('namespace nArrayMulDataModule'):]
nodes = {n: (int(w), b) for n,w,b in re.findall(r'def (v\d+) \(s : State\) \(i : Inputs\) : BitVec (\d+) := (.*)', text)}
instances = {n: {'module': m, 'inputs': re.findall(r'nio_5Fin_5F\d+ := ([^,}]+)', b)}
             for n,m,b in re.findall(r'def (inst_\w+)Inputs \(s : State\) \(i : Inputs\) : (\w+)\.Inputs := (.*)', text)}
assert len(instances) == 1499

def signal(expr):
    out = re.search(r'(inst_\w+)Eval s i\)?\.output.nio_5Fout_5F(\d+)', expr)
    if out: return out[1], int(out[2] != '0')
    reg = re.search(r's\.(g\d+\.r\w+)', expr)
    if reg: return reg[1], 0
    node = re.fullmatch(r'\((v\d+) s i\)', expr.strip())
    if node:
        width, body = nodes[node[1]]
        assert 'BitVec.ofNat' in body, (expr, body)
        return None
    raise ValueError(expr)

edges = defaultdict(list)
def equal(a, b):
    if a is None or b is None: return
    x, dx = a; y, dy = b
    edges[x].append((y, dx-dy))
    edges[y].append((x, dy-dx))
for name, inst in instances.items():
    for expr in inst['inputs']: equal((name,0), signal(expr))
first = {}; second = {}
for n, (width, body) in nodes.items():
    match = re.fullmatch(r'if i.nio_5FregEnables_5F([01]) = 1 then (.*) else s\.(g\d+\.r\w+)', body)
    if not match or width != 1: continue
    stage, source, field = match.groups()
    if field.endswith('nresultKnown'): continue
    (first if stage == '0' else second)[field] = source
    if stage == '1': equal((field,0), signal(source))
assert len(first) == 2278 and len(second) == 256
weights = {}; queue = deque()
def assign(node, value):
    if node in weights:
        assert weights[node] == value, (node,weights[node],value)
    else:
        weights[node] = value; queue.append(node)
# The two final concatenations are ordered from most to least significant bit.
atom = r'inst_\w+Eval s i\)?\.output.nio_5Fout_5F\d+|s\.g\d+\.r\w+|v\d+ s i'
for output in ('v5368','v5370'):
    offset = 0
    for token in reversed(re.findall(atom, nodes[output][1])):
        if token.startswith('v'):
            width, body = nodes[token.split()[0]]
            assert re.fullmatch(r'BitVec.ofNat \d+ 0',body)
            offset += width
        else:
            node, delta = signal(token)
            assign(node,offset-delta); offset += 1
    assert offset == 130
while queue:
    node = queue.popleft()
    for other, delta in edges[node]: assign(other,weights[node]+delta)
assert all(n in weights for n in instances)
assert all(n in weights for n in first)
assert all(n in weights for n in second)

def stage(name):
    if 'stage' in instances[name]: return instances[name]['stage']
    stages = set()
    for expr in instances[name]['inputs']:
        sig = signal(expr)
        if sig is None: continue
        node, _ = sig
        stages.add(stage(node) if node in instances else int(node in second))
    assert len(stages) == 1, (name,stages)
    result, = stages
    instances[name]['stage'] = result
    return result
for name, inst in instances.items():
    inst['column'] = weights[name]; stage(name)
report = {'instances': instances, 'first_registers': {n: weights[n] for n in first},
          'second_registers': {n: weights[n] for n in second}}
dest = root/'build/lean-hierarchical/array-tree-connections.json'
dest.write_text(json.dumps(report, indent=2)+'\n')
print(f'Checked weights and pipeline segments for {len(instances)} compressors, '
      f'{len(first)} first-stage bits and {len(second)} second-stage bits')

from collections import Counter
states = dict(re.findall(r'def (inst_\w+)Eval .*? := \w+\.evalSpec (s\.g\d+\.inst_\w+) ', text))
def wire(expr):
    out = re.search(r'(inst_\w+)Eval s i\)?\.output.nio_5Fout_5F(\d+)', expr)
    if out: return f'({out[1]}Eval s i).output.nio_5Fout_5F{out[2]}'
    reg = re.search(r's\.(g\d+\.r\w+)', expr)
    if reg: return 's.'+reg[1]
    ref = re.fullmatch(r'\((v\d+) s i\)',expr.strip())
    assert ref and re.fullmatch(r'BitVec.ofNat 1 [01]',nodes[ref[1]][1]),expr
    return None if nodes[ref[1]][1].endswith(' 0') else expr.strip()

def total(terms):
    return ' + '.join((f'{n} * ' if n != 1 else '')+f'({expr}).toNat' for expr,n in terms.items() if n) or '0'
columns = defaultdict(list)
for name, inst in instances.items(): columns[(inst['stage'],inst['column'])].append(name)
proofdir = root/'lean-hierarchical/Proofs/ArrayTreeColumns'
proofdir.mkdir(exist_ok=True)
imports = []
column_terms = {}
for (segment,column), names in sorted(columns.items()):
    label = f'Stage{segment}Column{column:03d}'
    imports.append(f'import Proofs.ArrayTreeColumns.{label}')
    incoming = Counter(); outgoing = Counter(); proof = []; balances = []
    for index,name in enumerate(names):
        inst = instances[name]
        lemma = {'nC22':'c22_sum','nC32':'c32_sum','nC53':'c53_sum'}[inst['module']]
        inputs = Counter(wire(x) for x in inst['inputs'] if wire(x) is not None)
        outputs = Counter({f'({name}Eval s i).output.nio_5Fout_5F0':1,
                           f'({name}Eval s i).output.nio_5Fout_5F1':2})
        if inst['module'] == 'nC53': outputs[f'({name}Eval s i).output.nio_5Fout_5F2'] = 2
        incoming.update(inputs); outgoing.update(outputs); balances.append((inputs, outputs))
        proof += [f'  have h{index} := {lemma} {states[name]} ({name}Inputs s i)',
                  f'  change {total(outputs)} = _ at h{index}',
                  f'  simp only [{name}Inputs, v6, v3021] at h{index}']
    common = incoming & outgoing
    incoming.subtract(common); outgoing.subtract(common)
    column_terms[(segment,column)] = (incoming + Counter(), outgoing + Counter())
    in_name = f'tree{segment}Column{column}Input'; out_name = f'tree{segment}Column{column}Output'
    lines = ['import Generated.ArrayMulDataModule', 'import Proofs.ArrayCompressors', '',
             'namespace HierarchicalArray', 'open DesignnArrayMulDataModule.nArrayMulDataModule', '',
             f'def {in_name} (s : State) (i : Inputs) : Nat :=', '  '+total(incoming), '',
             f'def {out_name} (s : State) (i : Inputs) : Nat :=', '  '+total(outgoing), '',
             f'theorem tree_{segment}_column_{column} (s : State) (i : Inputs) :',
             f'    {in_name} s i = {out_name} s i := by']
    wires = sorted(set().union(*(set(a) | set(b) for a,b in balances)))
    variables = {wire: f'x{j}' for j,wire in enumerate(wires)}
    def abstract(terms):
        return ' + '.join((f'{n} * ' if n != 1 else '') + variables[e] for e,n in terms.items() if n) or '0'
    arithmetic = ['private theorem arithmetic (' + ' '.join(variables.values()) + ' : Nat)']
    arithmetic += [f'    (h{j} : {abstract(b)} = {abstract(a)})' for j,(a,b) in enumerate(balances)]
    arithmetic += [f'    : {abstract(incoming)} = {abstract(outgoing)} := by omega', '']
    lines[6:6] = arithmetic
    lines += proof + [f'  unfold {in_name} {out_name}',
                      '  exact arithmetic ' + ' '.join(f'({w}).toNat' for w in wires) +
                      ' ' + ' '.join(f'h{j}' for j in range(len(names))), '', 'end HierarchicalArray', '']
    (proofdir/(label+'.lean')).write_text('\n'.join(lines))
(root/'lean-hierarchical/Proofs/ArrayTreeColumns.lean').write_text('\n'.join(imports)+'\n')
print(f'Generated {len(columns)} column contracts from reusable compressor theorems')

normaldir = root/'lean-hierarchical/Proofs/ArrayColumnCarry'
normaldir.mkdir(exist_ok=True)
imports = []
boundary_terms = {}
for segment in (0,1):
    for column in range(130):
        inc,out = column_terms.get((segment,column),(Counter(),Counter()))
        prev = column_terms.get((segment,column-1),(Counter(),Counter()))[1]
        carry_in = Counter({e:n//2 for e,n in prev.items() if 'out_5F1' in e or 'out_5F2' in e})
        carry_out = Counter({e:n//2 for e,n in out.items() if 'out_5F1' in e or 'out_5F2' in e})
        consumed = Counter({e:n for e,n in inc.items() if 'inst_' in e})
        assert not (consumed - carry_in), (segment,column,consumed-carry_in)
        boundary_in = inc - consumed
        boundary_out = out - Counter({e:2*n for e,n in carry_out.items()})
        boundary_out.update(carry_in-consumed)
        boundary_terms[(segment,column)] = (boundary_in,boundary_out)
        label = f'Stage{segment}Column{column:03d}'
        imports.append('import Proofs.ArrayColumnCarry.'+label)
        prefix = f'column{segment}_{column}'
        values = [('Input',boundary_in),('Output',boundary_out),('CarryIn',carry_in),('CarryOut',carry_out)]
        wires = sorted(set(inc)|set(out)|set(carry_in))
        variables = {w:f'x{j}' for j,w in enumerate(wires)}
        def abstract(terms):
            return ' + '.join((f'{n} * ' if n != 1 else '')+variables[e] for e,n in terms.items() if n) or '0'
        source = 'Proofs.ArrayTreeColumns.'+label if (segment,column) in column_terms else 'Generated.ArrayMulDataModule'
        lines = ['import '+source,'', 'namespace HierarchicalArray',
                 'open DesignnArrayMulDataModule.nArrayMulDataModule','']
        if wires:
            lines += ['private theorem balance ('+' '.join(variables.values())+' : Nat)',
                      f'    (h : {abstract(inc)} = {abstract(out)}) :',
                      f'    ({abstract(boundary_in)}) + ({abstract(carry_in)}) =',
                      f'      ({abstract(boundary_out)}) + 2 * ({abstract(carry_out)}) := by',
                      '  calc',
                      f'    _ = ({abstract(inc)}) + ({abstract(carry_in-consumed)}) := by (try simp only [Nat.add_zero]); all_goals ac_rfl',
                      f'    _ = ({abstract(out)}) + ({abstract(carry_in-consumed)}) := congrArg (fun x => x + ({abstract(carry_in-consumed)})) h',
                      '    _ = _ := by (try simp only [Nat.mul_add, Nat.add_zero]); all_goals ac_rfl','']
        for suffix,terms in values:
            lines += [f'def {prefix}{suffix} (s : State) (i : Inputs) : Nat :=', '  '+total(terms),'']
        lines += [f'theorem {prefix}_balance (s : State) (i : Inputs) :',
                  f'    {prefix}Input s i + {prefix}CarryIn s i =',
                  f'      {prefix}Output s i + 2 * {prefix}CarryOut s i := by']
        if wires:
            lines += [f'  have h := tree_{segment}_column_{column} s i',
                      f'  unfold tree{segment}Column{column}Input tree{segment}Column{column}Output at h',
                      '  exact balance '+' '.join(f'({w}).toNat' for w in wires)+' h']
        else: lines += ['  rfl']
        lines += ['', 'end HierarchicalArray','']
        (normaldir/(label+'.lean')).write_text('\n'.join(lines))
(root/'lean-hierarchical/Proofs/ArrayColumnCarry.lean').write_text('\n'.join(imports)+'\n')
print('Generated 260 column contracts with explicit incoming and outgoing carries')

for segment in (0,1):
    lines = ['import Proofs.ArrayColumnCarry', 'import Proofs.BinaryColumns', '',
             'set_option maxRecDepth 8192', 'set_option maxHeartbeats 2000000', '',
             'namespace HierarchicalArray', 'open DesignnArrayMulDataModule.nArrayMulDataModule', '']
    for label in ('Input','Output','Carry'):
        lines += [f'def stage{segment}{label} (s : State) (i : Inputs) : Nat → Nat']
        for column in range(130):
            suffix = 'CarryIn' if label == 'Carry' else label
            lines += [f'  | {column} => column{segment}_{column}{suffix} s i']
        if label == 'Carry': lines += [f'  | 130 => column{segment}_129CarryOut s i']
        lines += ['  | _ => 0', '']
    lines += [f'theorem stage{segment}_columns (s : State) (i : Inputs) (k : Nat) (bound : k < 130) :',
              f'    stage{segment}Input s i k + stage{segment}Carry s i k =',
              f'      stage{segment}Output s i k + 2 * stage{segment}Carry s i (k + 1) := by',
              '  have cases : '+' ∨ '.join(f'k = {k}' for k in range(130))+' := by omega',
              '  rcases cases with '+' | '.join('h' for _ in range(130))+' <;> subst k']
    lines += [f'  · exact column{segment}_{k}_balance s i' for k in range(130)]
    lines += ['', '/-- Weighted conservation for the compressor network in this pipeline segment.',
              '    Wires bypassing every compressor can be added equally to both sides. -/',
              f'theorem stage{segment}_weighted_conservation (s : State) (i : Inputs) :',
              f'    BitVec.ofNat 130 (HierarchicalColumns.weighted 130 (stage{segment}Input s i)) =',
              f'      BitVec.ofNat 130 (HierarchicalColumns.weighted 130 (stage{segment}Output s i)) := by',
              f'  exact HierarchicalColumns.truncated_conservation 130 (stage{segment}Input s i)',
              f'    (stage{segment}Output s i) (stage{segment}Carry s i) (stage{segment}_columns s i) rfl', '',
              'end HierarchicalArray', '']
    def split_cases(lo, hi, depth):
        pad = '  ' + '  '*depth
        if hi-lo == 1:
            return [pad+f'have hk : k = {lo} := by omega', pad+'subst k',
                    pad+f'exact column{segment}_{lo}_balance s i']
        mid = (lo+hi)//2
        return [pad+f'by_cases h{depth} : k < {mid}', pad+'·'] + split_cases(lo,mid,depth+1) + [pad+'·'] + split_cases(mid,hi,depth+1)
    start = next(j for j,line in enumerate(lines) if line.startswith('  have cases :'))
    lines[start:start+132] = split_cases(0,130,0)
    (root/f'lean-hierarchical/Proofs/ArrayTreeStage{segment}.lean').write_text('\n'.join(lines))
print('Generated both pipeline-segment weighted conservation theorems')

boundarydir = root/'lean-hierarchical/Proofs/ArrayRegisterBoundary'
boundarydir.mkdir(exist_ok=True)
next_nodes = {}
for node,(width,body) in nodes.items():
    match = re.fullmatch(r'if i.nio_5FregEnables_5F1 = 1 then (.*) else s\.(g\d+\.r\w+)',body)
    if match and width == 1 and match[2] in second: next_nodes[match[2]] = node
imports=[]
for col in range(130):
    regs=[r for r in second if weights[r] == col]
    state_values=Counter('s.'+r for r in regs)
    source_values=Counter(wire(second[r]) for r in regs)
    assert source_values == boundary_terms[(0,col)][1]
    bypass=state_values-boundary_terms[(1,col)][0]
    assert not (boundary_terms[(1,col)][0]-state_values)
    label=f'Column{col:03d}'; imports.append('import Proofs.ArrayRegisterBoundary.'+label)
    name=f'secondRegisterColumn{col}'
    lines=[f'import Proofs.ArrayColumnCarry.Stage0Column{col:03d}',
           f'import Proofs.ArrayColumnCarry.Stage1Column{col:03d}', '',
           'namespace HierarchicalArray','open DesignnArrayMulDataModule.nArrayMulDataModule','',
           f'def {name} (s : State) : Nat :=','  '+total(state_values),'',
           f'def bypassColumn{col} (s : State) : Nat :=','  '+total(bypass),'',
           f'theorem second_column_{col}_capture (s : State) (i : Inputs)',
           '    (enabled : i.nio_5FregEnables_5F1 = 1) :',
           f'    {name} (step s i) = column0_{col}Output s i := by',
           f'  simp only [{name}, step, eval_eq_spec]',
           '  change '+total(Counter(f'({next_nodes[r]} s i)' for r in regs))+' = _',
           '  simp only ['+', '.join(next_nodes[r] for r in regs)+f', enabled, if_true, column0_{col}Output]',
           '  all_goals ac_rfl','',
           f'theorem second_column_{col}_input (s : State) (i : Inputs) :',
           f'    {name} s = column1_{col}Input s i + bypassColumn{col} s := by',
           f'  simp only [{name}, column1_{col}Input, bypassColumn{col}, Nat.add_zero, Nat.zero_add]',
           '  all_goals ac_rfl','','end HierarchicalArray','']
    (boundarydir/(label+'.lean')).write_text('\n'.join(lines))
(root/'lean-hierarchical/Proofs/ArrayRegisterBoundary.lean').write_text('\n'.join(imports)+'\n')
print('Generated columnwise second-register capture and bypass contracts')

lines=['import Generated.ArrayMulDataModule','import Proofs.BinaryPacking','',
       'set_option maxRecDepth 8192','set_option maxHeartbeats 2000000','',
       'namespace HierarchicalArray','open DesignnArrayMulDataModule.nArrayMulDataModule',
       'open HierarchicalColumns','']
output_bits = {}
for node,label in [('v5368','outputSumBit'),('v5370','outputCarryBit')]:
    bits=[]
    for token in reversed(re.findall(atom,nodes[node][1])):
        if token.startswith('v'):
            width,body=nodes[token.split()[0]]
            assert re.fullmatch(r'BitVec.ofNat \d+ 0',body)
            bits += ['0#1']*width
        else: bits.append(wire(token))
    assert len(bits)==130
    output_bits[label] = bits
    used = [k for k,e in enumerate(bits) if e != '0#1']
    pad = min(used)
    packed = f'x{used[-1]}'
    for k in reversed(used[:-1]): packed = f'({packed} ++ x{k})'
    if pad: packed = f'({packed} ++ 0#{pad})'
    expanded = '0#0'
    for k in reversed(range(130)):
        expanded = f'({expanded} ++ ' + (f'x{k}' if k in used else '0#1') + ')'
    function = '(bitAt [' + ', '.join(f'x{k}' if k in used else '0#1' for k in range(130)) + '])'
    lines += [f'private theorem {label}_arithmetic (' + ' '.join(f'x{k}' for k in used) + ' : BitVec 1) :',
              f'    {packed} = pack 130 {function} := by',
              '  apply Eq.trans (b := packList [' + ', '.join(f'x{k}' if k in used else '0#1' for k in range(130)) + '])', f'  · change {packed} = {expanded}', '    bv_decide', '  · exact (pack_list [' + ', '.join(f'x{k}' if k in used else '0#1' for k in range(130)) + ']).symm', '']
    lines += [f'def {label} (s : State) (i : Inputs) : Nat → BitVec 1 :=', '  bitAt [' + ', '.join(bits) + ']']
    lines += ['',f'theorem {label}_pack (s : State) (i : Inputs) :',
              f'    {node} s i = pack 130 ({label} s i) := by',
              '  exact '+label+'_arithmetic '+ ' '.join('('+bits[k]+')' for k in used),'']
lines += ['def outputColumnValue (s : State) (i : Inputs) (k : Nat) : Nat :=',
          '  (outputSumBit s i k).toNat + (outputCarryBit s i k).toNat','',
          'theorem output_weighted_columns (s : State) (i : Inputs) :',
          '    (observe s i).nio_5Fresult = BitVec.ofNat 130 (weighted 130 (outputColumnValue s i)) := by',
          '  simp only [observe, eval_eq_spec]',
          '  change v5371 s i = _',
          '  rw [v5371, outputSumBit_pack, outputCarryBit_pack, pack_eq_weighted, pack_eq_weighted,',
          '    ← BitVec.ofNat_add, ← weighted_add]',
          '  rfl','','end HierarchicalArray','']
(root/'lean-hierarchical/Proofs/ArrayOutputPacking.lean').write_text('\n'.join(lines))

outputdir=root/'lean-hierarchical/Proofs/ArrayOutputColumns'
outputdir.mkdir(exist_ok=True)
imports=[]
for col in range(130):
    actual=Counter(bits[col] for bits in output_bits.values() if bits[col] != '0#1')
    registers=Counter('s.'+r for r in second if weights[r] == col)
    bypass=registers-boundary_terms[(1,col)][0]
    expected=boundary_terms[(1,col)][1]+bypass
    assert actual == expected,(col,actual,expected)
    label=f'Column{col:03d}'; imports.append('import Proofs.ArrayOutputColumns.'+label)
    lines=['import Proofs.ArrayOutputPacking',f'import Proofs.ArrayRegisterBoundary.Column{col:03d}','',
           'namespace HierarchicalArray','open DesignnArrayMulDataModule.nArrayMulDataModule','',
           f'theorem output_column_{col} (s : State) (i : Inputs) :',
           f'    outputColumnValue s i {col} = column1_{col}Output s i + bypassColumn{col} s := by',
           f'  simp only [outputColumnValue, outputSumBit, outputCarryBit, HierarchicalColumns.bitAt, column1_{col}Output,',
           f'    bypassColumn{col}, BitVec.toNat_ofNat, Nat.add_zero, Nat.zero_add]',
           '  all_goals ac_rfl','','end HierarchicalArray','']
    (outputdir/(label+'.lean')).write_text('\n'.join(lines))
(root/'lean-hierarchical/Proofs/ArrayOutputColumns.lean').write_text('\n'.join(imports)+'\n')
print('Checked and generated all 130 output-column wiring contracts')

capturecols=root/'lean-hierarchical/Proofs/ArrayInputColumns'
capturecols.mkdir(exist_ok=True)
first_next={}
for node,(width,body) in nodes.items():
    match=re.fullmatch(r'if i.nio_5FregEnables_5F0 = 1 then (.*) else s\.(g\d+\.r\w+)',body)
    if match and width == 1: first_next[match[2]]=node
imports=[]
for col in range(130):
    inc=boundary_terms[(0,col)][0]
    nxt=Counter(); captured=Counter(); defs=[]
    for expr,count in inc.items():
        if expr.startswith('s.'):
            reg=expr[2:]; node=first_next[reg]
            nxt[f'({node} s i)'] += count
            captured[first[reg]] += count
            defs.append(node)
        else:
            assert expr=='(v3021 s i)',expr
            nxt[expr]+=count; captured[expr]+=count
    label=f'Column{col:03d}'; imports.append('import Proofs.ArrayInputColumns.'+label)
    name=f'capturedInputColumn{col}'
    lines=[f'import Proofs.ArrayColumnCarry.Stage0Column{col:03d}','',
           'namespace HierarchicalArray','open DesignnArrayMulDataModule.nArrayMulDataModule','',
           f'def {name} (s : State) (i : Inputs) : Nat :=','  '+total(captured),'']
    for action,enable,rhs in [('capture',1,f'{name} s i'),('hold',0,f'column0_{col}Input s i')]:
        lines += [f'theorem input_column_{col}_{action} (s : State) (i later : Inputs)',
                  f'    (enabled : i.nio_5FregEnables_5F0 = {enable}) :',
                  f'    column0_{col}Input (step s i) later = {rhs} := by',
                  f'  simp only [column0_{col}Input, step, eval_eq_spec]',
                  '  change '+total(nxt)+' = _',
                  '  simp only ['+', '.join(defs+[name,'v3021','enabled'])+']',
                  '  all_goals rfl','']
    lines += ['end HierarchicalArray','']
    (capturecols/(label+'.lean')).write_text('\n'.join(lines))
(root/'lean-hierarchical/Proofs/ArrayInputColumns.lean').write_text('\n'.join(imports)+'\n')
print('Generated first-register input-column capture and hold contracts')

# Independently account for every captured input bit in the packed Booth rows.
raw_nodes=['v13']+[n for n,(w,b) in nodes.items() if w==66 and re.fullmatch(r'if \(v\d+ s i\) = 1 then \(v38 s i\) else \(v\d+ s i\)',b)]
assert len(raw_nodes)==33
correction_nodes=[]
for index,raw in enumerate(raw_nodes):
    if index==0: correction_nodes.append('v23'); continue
    cond=re.match(r'if \((v\d+) s i\)',nodes[raw][1])[1]
    corr,=[n for n,(w,b) in nodes.items() if w==2 and b.startswith(f'if ({cond} s i) = 1 then (v19 s i)')]
    correction_nodes.append(corr)
leaves={n:[f'raw{k}.{j}' for j in range(66)] for k,n in enumerate(raw_nodes)}
leaves.update({n:[f'correction{k}.{j}' for j in range(2)] for k,n in enumerate(correction_nodes)})
def bit_symbols(node):
    if node in leaves: return leaves[node]
    width,body=nodes[node]
    constant=re.fullmatch(r'BitVec.ofNat \d+ (\d+)',body)
    if constant: result=[str((int(constant[1])>>j)&1) for j in range(width)]
    else:
        extract=re.fullmatch(r"BitVec.extractLsb' (\d+) (\d+) \((v\d+) s i\)",body)
        invert=re.fullmatch(r'\(\((v\d+) s i\) \^\^\^ \((v\d+) s i\)\)',body)
        if extract:
            start,size,source=extract.groups();result=bit_symbols(source)[int(start):int(start)+int(size)]
        elif invert:
            left,right=map(bit_symbols,invert.groups())
            def xor(a,b):
                if a=='0':return b
                if b=='0':return a
                if a=='1':return ('0' if b=='1' else '!'+b)
                if b=='1':return '!'+a
                raise ValueError((a,b))
            result=[xor(a,b) for a,b in zip(left,right)]
        else: raise ValueError((node,body))
    assert len(result)==width,(node,width,result)
    leaves[node]=result
    return result
expected=[Counter() for _ in range(130)]
for k,raw in enumerate(raw_nodes):
    bits=bit_symbols(raw);sign=bits[65]
    if k==0: row=bits+[sign,sign,'!'+sign];weight=0
    else:
        row=bit_symbols(correction_nodes[k-1])+bits+['!'+sign]+([] if k==32 else ['1'])
        weight=2*k-2
    for j,bit in enumerate(row):
        if weight+j<130 and bit!='0':expected[weight+j][bit]+=1
for j,bit in enumerate(bit_symbols(correction_nodes[32])):expected[64+j][bit]+=1
for col in range(130):
    actual=Counter()
    for expr,count in boundary_terms[(0,col)][0].items():
        source=first[expr[2:]] if expr.startswith('s.') else expr
        node=re.fullmatch(r'\((v\d+) s i\)',source)[1]
        bit,=bit_symbols(node)
        if bit!='0':actual[bit]+=count
    assert actual==expected[col],(col,actual-expected[col],expected[col]-actual)
print('Checked all captured input bits against the 33 packed Booth rows and final correction')

inputwires=root/'lean-hierarchical/Proofs/ArrayInputWiring'
inputwires.mkdir(exist_ok=True)
leaf_names=set(raw_nodes+correction_nodes)
def source_defs(n,seen):
    if n in seen or n in leaf_names:return
    seen.add(n)
    for dep in re.findall(r'\b(v\d+) s i',nodes[n][1]):source_defs(dep,seen)
def canonical_bit(bit):
    if bit in ('0','1'):return bit+'#1'
    negative=bit.startswith('!'); bit=bit.lstrip('!')
    category,index=bit.split('.')
    if category.startswith('raw'):node=raw_nodes[int(category[3:])]
    else:node=correction_nodes[int(category[10:])]
    expr=f'BitVec.extractLsb\' {index} 1 ({node} s i)'
    return f'(~~~({expr}))' if negative else f'({expr})'
imports=[]
for col in range(130):
    defs=set()
    for expr in boundary_terms[(0,col)][0]:
        source=first[expr[2:]] if expr.startswith('s.') else expr
        source_defs(re.fullmatch(r'\((v\d+) s i\)',source)[1],defs)
    label=f'Column{col:03d}';imports.append('import Proofs.ArrayInputWiring.'+label)
    canonical=Counter({canonical_bit(bit):count for bit,count in expected[col].items()})
    lines=[f'import Proofs.ArrayInputColumns.Column{col:03d}','import Std.Tactic','',
           'namespace HierarchicalArray','open DesignnArrayMulDataModule.nArrayMulDataModule','',
           'private theorem xor_one (x : BitVec 1) : x ^^^ 1#1 = ~~~x := by bv_decide','',
           f'def boothInputColumn{col} (s : State) (i : Inputs) : Nat :=','  '+total(canonical),'',
           f'theorem captured_input_column_{col} (s : State) (i : Inputs) :',
           f'    capturedInputColumn{col} s i = boothInputColumn{col} s i := by',
           f'  simp only [capturedInputColumn{col}, boothInputColumn{col}, '+', '.join(sorted(defs,key=lambda n:int(n[1:])))+', xor_one]',
           '  all_goals ac_rfl','','end HierarchicalArray','']
    (inputwires/(label+'.lean')).write_text('\n'.join(lines))
(root/'lean-hierarchical/Proofs/ArrayInputWiring.lean').write_text('\n'.join(imports)+'\n')
print('Generated Lean contracts connecting captured source bits to canonical Booth row bits')

lines=['import Proofs.ArrayOutputColumns','import Proofs.ArrayTreeStage1','',
       'set_option maxRecDepth 8192','set_option maxHeartbeats 2000000','',
       'namespace HierarchicalArray','open DesignnArrayMulDataModule.nArrayMulDataModule',
       'open HierarchicalColumns','',
       'def secondColumns (s : State) : Nat → Nat :=',
       '  columnAt ['+', '.join(f'secondRegisterColumn{k} s' for k in range(130))+']','',
       'def bypassColumns (s : State) : Nat → Nat :=',
       '  columnAt ['+', '.join(f'bypassColumn{k} s' for k in range(130))+']','']
def dispatch(lo,hi,depth,leaf):
    pad='  '+'  '*depth
    if hi-lo==1:return [pad+f'have hk : k = {lo} := by omega',pad+'subst k',pad+leaf(lo)]
    mid=(lo+hi)//2
    return [pad+f'by_cases h{depth} : k < {mid}',pad+'·']+dispatch(lo,mid,depth+1,leaf)+[pad+'·']+dispatch(mid,hi,depth+1,leaf)
lines += ['theorem second_columns_input (s : State) (i : Inputs) (k : Nat) (bound : k < 130) :',
          '    secondColumns s k = stage1Input s i k + bypassColumns s k := by']
lines += dispatch(0,130,0,lambda k:f'exact second_column_{k}_input s i')
lines += ['', 'theorem output_columns_boundary (s : State) (i : Inputs) (k : Nat) (bound : k < 130) :',
          '    outputColumnValue s i k = stage1Output s i k + bypassColumns s k := by']
lines += dispatch(0,130,0,lambda k:f'exact output_column_{k} s i')
lines += ['', '/-- The actual output is the weighted sum of the second-stage registers,',
          '    including the five low bits that bypass the last compressor layer. -/',
          'theorem output_from_second_registers (s : State) (i : Inputs) :',
          '    (observe s i).nio_5Fresult = BitVec.ofNat 130 (weighted 130 (secondColumns s)) := by',
          '  rw [output_weighted_columns]',
          '  have outputs := weighted_congr 130 (outputColumnValue s i)',
          '    (fun k => stage1Output s i k + bypassColumns s k) (output_columns_boundary s i)',
          '  have registers := weighted_congr 130 (secondColumns s)',
          '    (fun k => stage1Input s i k + bypassColumns s k) (second_columns_input s i)',
          '  rw [outputs, registers, weighted_add, weighted_add, BitVec.ofNat_add, BitVec.ofNat_add,',
          '    stage1_weighted_conservation]', '',
          'theorem output_input_independent (s : State) (i later : Inputs) :',
          '    (observe s i).nio_5Fresult = (observe s later).nio_5Fresult := by',
          '  rw [output_from_second_registers, output_from_second_registers]', '',
          'end HierarchicalArray','']
(root/'lean-hierarchical/Proofs/ArrayOutputContract.lean').write_text('\n'.join(lines))
print('Generated complete output-to-second-register weighted contract')

lines=['import Proofs.ArrayOutputContract','import Proofs.ArrayTreeStage0',
       'import Proofs.ArrayInputColumns','',
       'set_option maxRecDepth 8192','set_option maxHeartbeats 2000000','',
       'namespace HierarchicalArray','open DesignnArrayMulDataModule.nArrayMulDataModule',
       'open HierarchicalColumns','',
       'def capturedColumns (s : State) (i : Inputs) : Nat → Nat :=',
       '  columnAt ['+', '.join(f'capturedInputColumn{k} s i' for k in range(130))+']','',
       'theorem second_columns_capture (s : State) (i : Inputs)',
       '    (enabled : i.nio_5FregEnables_5F1 = 1) (k : Nat) (bound : k < 130) :',
       '    secondColumns (step s i) k = stage0Output s i k := by']
lines += dispatch(0,130,0,lambda k:f'exact second_column_{k}_capture s i enabled')
lines += ['', 'theorem first_columns_capture (s : State) (i later : Inputs)',
          '    (enabled : i.nio_5FregEnables_5F0 = 1) (k : Nat) (bound : k < 130) :',
          '    stage0Input (step s i) later k = capturedColumns s i k := by']
lines += dispatch(0,130,0,lambda k:f'exact input_column_{k}_capture s i later enabled')
lines += ['', '/-- An enabled second edge transfers the old first-stage weighted value',
          '    through the compressor network into the actual output. -/',
          'theorem output_after_transfer (s : State) (i later : Inputs)',
          '    (enabled : i.nio_5FregEnables_5F1 = 1) :',
          '    (observe (step s i) later).nio_5Fresult =',
          '      BitVec.ofNat 130 (weighted 130 (stage0Input s i)) := by',
          '  rw [output_from_second_registers]',
          '  rw [weighted_congr 130 (secondColumns (step s i)) (stage0Output s i)',
          '    (second_columns_capture s i enabled)]',
          '  exact (stage0_weighted_conservation s i).symm', '',
          '/-- The first edge samples the operands; subsequent input changes do not',
          '    affect the result transferred by the enabled second edge. -/',
          'theorem two_edges_captured_columns (s : State) (first second later : Inputs)',
          '    (capture : first.nio_5FregEnables_5F0 = 1)',
          '    (transfer : second.nio_5FregEnables_5F1 = 1) :',
          '    (observe (step (step s first) second) later).nio_5Fresult =',
          '      BitVec.ofNat 130 (weighted 130 (capturedColumns s first)) := by',
          '  rw [output_after_transfer _ second later transfer]',
          '  rw [weighted_congr 130 (stage0Input (step s first) second) (capturedColumns s first)',
          '    (first_columns_capture s first second capture)]', '',
          'end HierarchicalArray','']
(root/'lean-hierarchical/Proofs/ArrayPipeline.lean').write_text('\n'.join(lines))
print('Generated two-edge datapath transfer contract')

# Preserve the Booth matrix explicitly, so column wiring and row arithmetic
# can be verified independently and joined by weighted_matrix_mod.
rows=[]
for k,raw in enumerate(raw_nodes):
    bits=bit_symbols(raw); sign=bits[65]
    if k==0: row=bits+[sign,sign,'!'+sign]; offset=0
    else:
        row=bit_symbols(correction_nodes[k-1])+bits+['!'+sign]+([] if k==32 else ['1'])
        offset=2*k-2
    rows.append((['0']*offset+row)[:130])
rows.append(['0']*64+bit_symbols(correction_nodes[32]))
lines=['import Proofs.BinaryMatrix','import Generated.ArrayMulDataModule.Part006','',
       'namespace HierarchicalArray','open DesignnArrayMulDataModule.nArrayMulDataModule',
       'open HierarchicalColumns','']
for k,row in enumerate(rows):
    lines += [f'def boothRowBits{k} (s : State) (i : Inputs) : List (BitVec 1) :=',
              '  ['+', '.join(canonical_bit(bit) for bit in row)+']','',
              f'def boothRowColumn{k} (s : State) (i : Inputs) (col : Nat) : Nat :=',
              f'  (bitAt (boothRowBits{k} s i) col).toNat','']
lines += ['def boothMatrix (s : State) (i : Inputs) : List (Nat → Nat) :=',
          '  ['+', '.join(f'boothRowColumn{k} s i' for k in range(34))+']','',
          'end HierarchicalArray','']
(root/'lean-hierarchical/Proofs/ArrayBoothMatrix.lean').write_text('\n'.join(lines))
folder=root/'lean-hierarchical/Proofs/ArrayMatrixColumns';folder.mkdir(exist_ok=True)
imports=[]
rowdefs=', '.join(f'boothRowColumn{k}, boothRowBits{k}' for k in range(34))
for col in range(130):
    label=f'Column{col:03d}';imports.append('import Proofs.ArrayMatrixColumns.'+label)
    lines=[f'import Proofs.ArrayInputWiring.Column{col:03d}','import Proofs.ArrayBoothMatrix','',
           'set_option maxRecDepth 8192','set_option maxHeartbeats 2000000','',
           'namespace HierarchicalArray','open DesignnArrayMulDataModule.nArrayMulDataModule',
           'open HierarchicalColumns','',
           f'theorem booth_matrix_column_{col} (s : State) (i : Inputs) :',
           f'    boothInputColumn{col} s i = sumColumns (boothMatrix s i) {col} := by',
           f'  simp only [boothInputColumn{col}, boothMatrix, sumColumns, {rowdefs},',
           '    bitAt, BitVec.toNat_ofNat, Nat.add_zero, Nat.zero_add]',
           '  all_goals ac_rfl','','end HierarchicalArray','']
    (folder/(label+'.lean')).write_text('\n'.join(lines))
(root/'lean-hierarchical/Proofs/ArrayMatrixColumns.lean').write_text('\n'.join(imports)+'\n')
print('Generated Booth matrix and column-to-row contracts')

rowfolder=root/'lean-hierarchical/Proofs/ArrayMatrixRows';rowfolder.mkdir(exist_ok=True)
imports=[]
for k,row in enumerate(rows):
    label=f'Row{k:03d}';imports.append('import Proofs.ArrayMatrixRows.'+label)
    def generic_bit(bit):
        expr=canonical_bit(bit)
        if k<33: expr=expr.replace(f'({raw_nodes[k]} s i)','raw')
        if k>0: expr=expr.replace(f'({correction_nodes[min(k-1,32)]} s i)','correction')
        return expr
    bits='['+', '.join(generic_bit(bit) for bit in row)+']'
    if k==0:
        params='(raw : BitVec 66)'; value='firstPacked raw'; actual=f'firstPacked ({raw_nodes[k]} s i)'
        args=f'({raw_nodes[k]} s i)'
    elif k<33:
        params='(raw : BitVec 66) (correction : BitVec 2)'
        value=f'nextPacked {"true" if k==32 else "false"} raw correction <<< {2*k-2}'
        args=f'({raw_nodes[k]} s i) ({correction_nodes[k-1]} s i)'
        actual=f'nextPacked {"true" if k==32 else "false"} ({raw_nodes[k]} s i) ({correction_nodes[k-1]} s i) <<< {2*k-2}'
    else:
        params='(correction : BitVec 2)';value='correction.setWidth 130 <<< 64'
        args=f'({correction_nodes[32]} s i)';actual=f'({correction_nodes[32]} s i).setWidth 130 <<< 64'
    lines=['import Proofs.ArrayBoothMatrix','import Proofs.BoothPackedSum','',
           'set_option maxRecDepth 8192','set_option maxHeartbeats 2000000','',
           'namespace HierarchicalArray','open DesignnArrayMulDataModule.nArrayMulDataModule',
           'open HierarchicalColumns HierarchicalBooth','',
           f'private theorem packed_row {params} :',
           f'    pack 130 (bitAt {bits}) = {value} := by',
           '  simp only [pack, bitAt, firstPacked, nextPacked]',
           '  bv_decide','',
           f'theorem booth_matrix_row_{k} (s : State) (i : Inputs) :',
           f'    BitVec.ofNat 130 (weighted 130 (boothRowColumn{k} s i)) = {actual} := by',
           f'  change BitVec.ofNat 130 (weighted 130 (fun col => (bitAt (boothRowBits{k} s i) col).toNat)) = _',
           '  rw [← pack_eq_weighted]',f'  exact packed_row {args}','',
           'end HierarchicalArray','']
    (rowfolder/(label+'.lean')).write_text('\n'.join(lines))
(root/'lean-hierarchical/Proofs/ArrayMatrixRows.lean').write_text('\n'.join(imports)+'\n')
print('Generated modular packed-row arithmetic contracts')

lines=['import Proofs.ArrayPipeline','import Proofs.ArrayMatrixColumns','',
       'set_option maxRecDepth 8192','set_option maxHeartbeats 2000000','',
       'namespace HierarchicalArray','open DesignnArrayMulDataModule.nArrayMulDataModule',
       'open HierarchicalColumns','',
       'theorem captured_matrix_column (s : State) (i : Inputs) (k : Nat) (bound : k < 130) :',
       '    capturedColumns s i k = sumColumns (boothMatrix s i) k := by']
lines += dispatch(0,130,0,lambda k:f'exact (captured_input_column_{k} s i).trans (booth_matrix_column_{k} s i)')
lines += ['', 'theorem captured_matrix_sum (s : State) (i : Inputs) :',
          '    BitVec.ofNat 130 (weighted 130 (capturedColumns s i)) =',
          '      ((boothMatrix s i).map (fun row => BitVec.ofNat 130 (weighted 130 row))).sum := by',
          '  rw [weighted_congr 130 (capturedColumns s i) (sumColumns (boothMatrix s i))',
          '    (captured_matrix_column s i), weighted_matrix_mod]', '',
          'end HierarchicalArray','']
(root/'lean-hierarchical/Proofs/ArrayMatrixInput.lean').write_text('\n'.join(lines))
print('Generated complete captured-column to matrix-sum bridge')

lines=['import Proofs.ArrayMatrixRows','import Proofs.ArrayPackedInput','',
       'set_option maxRecDepth 8192','set_option maxHeartbeats 2000000','',
       'namespace HierarchicalArray','open DesignnArrayMulDataModule.nArrayMulDataModule',
       'open HierarchicalColumns HierarchicalBooth','',
       'private theorem shift_scale (x : BitVec 130) (n : Nat) :',
       '    x <<< n = BitVec.ofNat 130 (2^n) * x := by',
       '  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.mul_comm]',
       '  congr 1',
       '  apply BitVec.eq_of_toNat_eq',
       '  simp only [BitVec.toNat_twoPow, BitVec.toNat_ofNat]','']
xs=' '.join(f'x{k}' for k in range(34))
lhs='['+', '.join('x0' if k==0 else f'(x{k} <<< {64 if k==33 else 2*k-2})' for k in range(34))+'].sum'
horner='0#130'
for k in reversed(range(1,33)):horner=f'(x{k} + 4#130 * {horner})'
rhs=f'x0 + {horner} + BitVec.ofNat 130 (4^32) * x33'
lines += [f'private theorem sum_rows ({xs} : BitVec 130) :',f'    {lhs} = {rhs} := by',
          '  simp only [List.sum_cons, List.sum_nil, shift_scale, BitVec.mul_add,',
          '    ← BitVec.mul_assoc, BitVec.ofNat_mul_ofNat, BitVec.mul_zero, BitVec.add_zero]',
          '  ac_rfl','',
          'theorem booth_matrix_packed (s : State) (i : Inputs) :',
          '    ((boothMatrix s i).map (fun row => BitVec.ofNat 130 (weighted 130 row))).sum =',
          '      packedInputSum s i := by',
          '  simp only [boothMatrix, List.map_cons, List.map_nil]',
          '  rw ['+', '.join(f'booth_matrix_row_{k}' for k in range(34))+']',
          '  unfold packedInputSum',
          '  simp only [weightedBits, rawRow, rowCorrection]',
          '  exact sum_rows _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _','',
          'end HierarchicalArray','']
(root/'lean-hierarchical/Proofs/ArrayMatrixArithmetic.lean').write_text('\n'.join(lines))
print('Generated matrix-to-packed-arithmetic bridge')

holdfolder=root/'lean-hierarchical/Proofs/ArrayRegisterHold';holdfolder.mkdir(exist_ok=True)
imports=[]
for col in range(130):
    regs=[r for r in second if weights[r]==col]
    label=f'Column{col:03d}';imports.append('import Proofs.ArrayRegisterHold.'+label)
    lines=[f'import Proofs.ArrayRegisterBoundary.Column{col:03d}','',
           'namespace HierarchicalArray','open DesignnArrayMulDataModule.nArrayMulDataModule','',
           f'theorem second_column_{col}_hold (s : State) (i : Inputs)',
           '    (disabled : i.nio_5FregEnables_5F1 = 0) :',
           f'    secondRegisterColumn{col} (step s i) = secondRegisterColumn{col} s := by',
           f'  simp only [secondRegisterColumn{col}, step, eval_eq_spec]',
           '  change '+total(Counter(f'({next_nodes[r]} s i)' for r in regs))+' = _',
           '  simp only ['+', '.join(next_nodes[r] for r in regs)+', disabled]',
           '  rfl','','end HierarchicalArray','']
    (holdfolder/(label+'.lean')).write_text('\n'.join(lines))
(root/'lean-hierarchical/Proofs/ArrayRegisterHold.lean').write_text('\n'.join(imports)+'\n')
lines=['import Proofs.ArrayArithmeticContract','import Proofs.ArrayRegisterHold','',
       'set_option maxRecDepth 8192','set_option maxHeartbeats 2000000','',
       'namespace HierarchicalArray','open DesignnArrayMulDataModule.nArrayMulDataModule',
       'open HierarchicalColumns','',
       'theorem second_columns_hold (s : State) (i : Inputs)',
       '    (disabled : i.nio_5FregEnables_5F1 = 0) (k : Nat) (bound : k < 130) :',
       '    secondColumns (step s i) k = secondColumns s k := by']
lines += dispatch(0,130,0,lambda k:f'exact second_column_{k}_hold s i disabled')
lines += ['', 'theorem first_columns_hold (s : State) (i later : Inputs)',
          '    (disabled : i.nio_5FregEnables_5F0 = 0) (k : Nat) (bound : k < 130) :',
          '    stage0Input (step s i) later k = stage0Input s i k := by']
lines += dispatch(0,130,0,lambda k:f'exact input_column_{k}_hold s i later disabled')
lines += ['', 'theorem output_hold (s : State) (i later : Inputs)',
          '    (disabled : i.nio_5FregEnables_5F1 = 0) :',
          '    (observe (step s i) later).nio_5Fresult = (observe s i).nio_5Fresult := by',
          '  rw [output_from_second_registers, output_from_second_registers,',
          '    weighted_congr 130 _ _ (second_columns_hold s i disabled)]','',
          'end HierarchicalArray','']
(root/'lean-hierarchical/Proofs/ArrayHold.lean').write_text('\n'.join(lines))
print('Generated register and output hold contracts')
