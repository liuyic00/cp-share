#!/usr/bin/env python3
"""Generate exact conservation proofs for the actual inter-stage compression tree.

Discover basic two/three-input compressors from the exported assertions, walk
backwards from ArrayOutput's second-stage inputs, and preserve signal weights.
Lean checks local truth tables, column cancellation, and prefix composition.
The parser is not part of the trusted base and emits no axioms.
"""
import pathlib, re, collections
root = pathlib.Path(__file__).resolve().parents[2] / 'verification'
source = '\n'.join((p.read_text() for p in sorted((root / 'lean/Generated/ArrayMulDataModule').glob('Part*.lean'))))
nodes = {int(n): (int(w), e) for n, w, e in re.findall('def v(\\d+) \\(s : State\\) \\(i : Inputs\\) : BitVec (\\d+) := ([^\\n]+)', source)}

def strip(e):
    while e.startswith('('):
        depth = 0
        for k, c in enumerate(e):
            depth += (c == '(') - (c == ')')
            if depth == 0:
                break
        if k != len(e) - 1:
            break
        e = e[1:-1]
    return e

def linear(e):
    e = strip(e)
    m = re.fullmatch('v(\\d+) s i', e)
    if m:
        n = int(m[1])
        w, body = nodes[n]
        if w == 1 and (not body.startswith('BitVec.ofNat')):
            return ({e: 1}, w)
        d, _ = linear(body)
        return (d, w)
    if re.fullmatch('s\\.g\\d+\\.r\\w+', e):
        return ({e: 1}, 1)
    m = re.fullmatch('BitVec.ofNat (\\d+) (\\d+)', e)
    if m:
        return ({'1#1': int(m[2])} if int(m[2]) else {}, int(m[1]))
    depth = 0
    for k, c in enumerate(e):
        depth += (c == '(') - (c == ')')
        if depth == 0 and e[k:k + 3] == ' + ':
            a, wa = linear(e[:k])
            b, wb = linear(e[k + 3:])
            assert wa == wb, (e, wa, wb)
            return (dict(collections.Counter(a) + collections.Counter(b)), wa)
        if depth == 0 and e[k:k + 4] == ' ++ ':
            a, wa = linear(e[:k])
            b, wb = linear(e[k + 4:])
            a = {t: c * 2 ** wb for t, c in a.items()}
            return (dict(collections.Counter(a) + collections.Counter(b)), wa + wb)
    raise ValueError(e)
checks = [int(n) for n in re.findall('theorem check_(\\d+)', '\n'.join((p.read_text() for p in sorted((root / 'lean/Proofs/ArrayCompressors').glob('Part*.lean')))))]
relations = []
for check in checks:
    m = re.fullmatch('if \\(v(\\d+) s i\\) = \\(v(\\d+) s i\\) then 1 else 0', nodes[check][1])
    a, b = map(int, m.groups())
    lhs, _ = linear(f'v{a} s i')
    rhs, _ = linear(f'v{b} s i')
    relations.append((check, lhs, rhs))
primitives = [r for r in relations if sum(r[1].values()) <= 3]
producers = collections.defaultdict(list)
for j, (c, a, b) in enumerate(primitives):
    for term in b:
        producers[term].append(j)
rows = (root / 'lean/Proofs/ArrayOutput.lean').read_text()
weights = {}
pending = []
for k in range(3):
    expr = re.search(f'def incomingRow{k} .*? :=\\n  ([^\\n]+)', rows)[1]
    leaves = re.findall('\\(v\\d+ s i\\)|\\(0#1\\)', expr)
    assert len(leaves) == 130
    for bit, term in enumerate(reversed(leaves)):
        if term == '(0#1)':
            continue
        term = strip(term)
        weights[term] = bit
        pending.append(term)
used = set()
pending = [(term, weight) for term, weight in weights.items()]
while pending:
    term, weight = pending.pop()
    if term not in producers or term.startswith('s.'):
        continue
    assert len(producers[term]) == 1
    j = producers[term][0]
    check, a, b = primitives[j]
    weight = weight - (b[term] == 2)
    if (j, weight) in used:
        continue
    used.add((j, weight))
    for t in a:
        if t == '1#1':
            continue
        pending.append((t, weight))

def atom(term):
    return f'({term}).toNat' if term != '1#1' else '1'

def nat_sum(terms):
    return ' + '.join((atom(t) if c == 1 else f'{c} * {atom(t)}' for t, c in sorted(terms.items()) if c)) or '0'

def expand_bit(term, frontier):
    if term in frontier or term == '1#1' or term.startswith('s.'):
        return f'({term})'
    n = int(re.fullmatch('v(\\d+) s i', term)[1])
    return '(' + re.sub('\\(v(\\d+) s i\\)', lambda m: expand_bit(f'v{m[1]} s i', frontier), nodes[n][1]) + ')'

def write(path, text):
    if not path.exists() or path.read_text() != text:
        path.write_text(text)
output = root / 'lean/Proofs/ArrayTree'
output.mkdir(exist_ok=True)
chosen = sorted({j for j, w in used}, key=lambda j: primitives[j][0])
modules = {j: k // 64 for k, j in enumerate(chosen)}
for batch in range((len(chosen) + 63) // 64):
    lines = ['import Generated.ArrayMulDataModule', '', 'namespace ArrayTree', 'open nArrayMulDataModule', 'set_option maxRecDepth 8192', '']
    for j in chosen[batch * 64:(batch + 1) * 64]:
        check, a, b = primitives[j]
        frontier = set(a)
        terms = sorted((t for t in a if t != '1#1'))
        expanded = {expand_bit(t, frontier): c for t, c in sorted(b.items())}
        rhs = ' + '.join((f'{t}.toNat' if c == 1 else f'{c} * {t}.toNat' for t, c in expanded.items()))
        abstract = nat_sum(a) + ' = ' + rhs
        for k, t in enumerate(terms):
            abstract = re.sub(re.escape(t) + '(?![A-Za-z0-9_])', f'cut{k}', abstract)
        assert not re.search('v\\d+ s i|s\\.g\\d+', abstract), abstract
        binders = ' '.join((f'(cut{k} : BitVec 1)' for k in range(len(terms))))
        lines += [f'theorem compressor_{check} (s : State) (i : Inputs) :', f'    {nat_sum(a)} = {nat_sum(b)} := by', f'  have localCorrect {binders} : {abstract} := by']
        for k in range(len(terms)):
            lines += [f'    have h{k} : cut{k} = 0 ∨ cut{k} = 1 := by bv_decide']
        lines += ['    ' + ' <;> '.join([f'rcases h{k} with rfl | rfl' for k in range(len(terms))] + ['decide']), '  exact localCorrect ' + ' '.join((f'({t})' for t in terms)), '']
    lines += ['end ArrayTree', '']
    write(output / f'Local{batch:03}.lean', '\n'.join(lines))
outs = [collections.Counter() for _ in range(130)]
for k in range(3):
    expr = re.search(f'def incomingRow{k} .*? :=\\n  ([^\\n]+)', rows)[1]
    for w, t in enumerate(reversed(re.findall('\\(v\\d+ s i\\)|\\(0#1\\)', expr))):
        if t != '(0#1)':
            outs[w][strip(t)] += 1
carry = [collections.Counter() for _ in range(130)]
inputs = [collections.Counter() for _ in range(130)]
residual = collections.Counter()
column_balance = []
for w in range(130):
    bal = collections.Counter()
    for j, weight in used:
        if weight != w:
            continue
        _, a, b = primitives[j]
        for t, c in a.items():
            bal[t] += c
        for t, c in b.items():
            bal[t] -= c
            if c == 2:
                carry[w][t] += 1
    column_balance.append(bal)
    for t, c in bal.items():
        inputs[w][t] += c
    for t, c in outs[w].items():
        inputs[w][t] += c
    for t, c in carry[w].items():
        inputs[w][t] += 2 * c
    if w:
        for t, c in carry[w - 1].items():
            inputs[w][t] -= c
assert all((c >= 0 and (t.startswith('s.') or t == '1#1') for terms in inputs for t, c in terms.items() if c))
lines = ['import Generated.ArrayMulDataModule', '', 'namespace ArrayTree', 'open nArrayMulDataModule', 'set_option linter.unusedVariables false', '']
for w in range(130):
    for label, terms in [('inputColumn', inputs[w]), ('outputColumn', outs[w]), ('carryColumn', carry[w])]:
        lines += [f'def {label}{w} (s : State) (i : Inputs) : Nat := {nat_sum(terms)}', '']
lines += ['end ArrayTree', '']
write(output / 'Boundary.lean', '\n'.join(lines))
column_data = []
for w in range(130):
    js = sorted((j for j, weight in used if weight == w))
    counter = collections.Counter()
    for j in js:
        _, a, b = primitives[j]
        for t, c in a.items():
            counter[t] += c
        for t, c in b.items():
            counter[t] -= c
    a = {t: c for t, c in counter.items() if c > 0}
    b = {t: -c for t, c in counter.items() if c < 0}
    column_data.append((js, a, b))
for batch in range(9):
    group = column_data[batch * 16:(batch + 1) * 16]
    imports = sorted({modules[j] for js, a, b in group for j in js})
    lines = ['import Proofs.ArrayTree.Boundary', 'import Proofs.ColumnSum'] + [f'import Proofs.ArrayTree.Local{k:03}' for k in imports] + ['', 'namespace ArrayTree', 'open nArrayMulDataModule', 'set_option linter.unusedVariables false', 'set_option linter.unusedSimpArgs false', 'set_option maxRecDepth 8192', 'set_option maxHeartbeats 4000000', '']
    for w, (js, a, b) in enumerate(group, start=batch * 16):

        def linear_proof(lhs, rhs, facts):
            terms = sorted({t for pair, _ in facts for d in pair for t in d} | set(lhs) | set(rhs))
            terms = [t for t in terms if t != '1#1']

            def abstract(d):
                result = nat_sum(d)
                for k, t in enumerate(terms):
                    result = result.replace(atom(t), f'x{k}')
                return result
            binders = ' '.join((f'(x{k} : Nat)' for k in range(len(terms))))
            hypotheses = ' '.join((f'(h{k} : {abstract(a)} = {abstract(b)})' for k, ((a, b), _) in enumerate(facts)))
            total = 'h0'
            for k in range(1, len(facts)):
                total = f'(ColumnSum.add_equalities {total} h{k})'
            all_left = collections.Counter()
            all_right = collections.Counter()
            for (a, b), _ in facts:
                all_left.update(a)
                all_right.update(b)
            common = all_left.copy()
            for t, c in lhs.items():
                common[t] -= c
            assert all((c >= 0 for c in common.values()))
            assert all((all_right[t] - rhs.get(t, 0) == c for t, c in common.items()))
            common_text = ' + '.join((atom(t) for t, c in sorted(common.items()) for _ in range(c))) or '0'
            for k, t in enumerate(terms):
                common_text = common_text.replace(atom(t), f'x{k}')
            full_left = ' + '.join((f'({abstract(a)})' for (a, b), _ in facts))
            full_right = ' + '.join((f'({abstract(b)})' for (a, b), _ in facts))
            return [f'  have combine {binders} {hypotheses} :', f'      {abstract(lhs)} = {abstract(rhs)} := by', f'    have total := {total}', f'    have canceled : ({abstract(lhs)}) + ({common_text}) = ({abstract(rhs)}) + ({common_text}) := by', '      calc', f'        _ = {full_left} := by (try simp only [Nat.two_mul, Nat.add_zero, Nat.zero_add]) <;> ac_rfl', f'        _ = {full_right} := total', '        _ = _ := by (try simp only [Nat.two_mul, Nat.add_zero, Nat.zero_add]) <;> ac_rfl', '    exact Nat.add_right_cancel canceled', '  exact combine ' + ' '.join((f'({atom(t)})' for t in terms)) + ' ' + ' '.join((f'({proof})' for _, proof in facts))]
        lines += [f'/-- Exact sum conservation in column {w}; carries have weight two. -/', f'theorem column_{w} (s : State) (i : Inputs) :', f'    {nat_sum(a)} = {nat_sum(b)} := by']
        facts = [((primitives[j][1], primitives[j][2]), f'compressor_{primitives[j][0]} s i') for j in js]
        lines += linear_proof(a, b, facts) if js else ['  rfl']
        lines += ['']
        prev = f'carryColumn{w - 1} s i' if w else '0'
        lhs = collections.Counter(inputs[w])
        if w:
            lhs.update(carry[w - 1])
        rhs = collections.Counter(outs[w])
        rhs.update({t: 2 * c for t, c in carry[w].items()})
        lines += [f'theorem boundary_{w} (s : State) (i : Inputs) :', f'    inputColumn{w} s i + {prev} = outputColumn{w} s i + 2 * carryColumn{w} s i := by']
        terms = sorted({t for d in [lhs, rhs, a, b] for t, c in d.items() if c and t != '1#1'})
        lhs_text = nat_sum(inputs[w]) + ' + (' + (nat_sum(carry[w - 1]) if w else '0') + ')'
        rhs_text = nat_sum(outs[w]) + ' + 2 * (' + nat_sum(carry[w]) + ')'
        equation = f'({lhs_text}) = ({rhs_text})'
        premise = f'{nat_sum(a)} = {nat_sum(b)}'
        for k, t in enumerate(terms):
            equation = equation.replace(atom(t), f'x{k}')
            premise = premise.replace(atom(t), f'x{k}')
        binders = ' '.join((f'(x{k} : Nat)' for k in range(len(terms))))
        common = collections.Counter(lhs)
        for t, c in a.items():
            common[t] -= c
        assert all((c >= 0 for c in common.values()))

        def abstract_boundary(d):
            result = nat_sum(d)
            for k, t in enumerate(terms):
                result = result.replace(atom(t), f'x{k}')
            return result
        middle_left = f'({abstract_boundary(a)}) + ({abstract_boundary(common)})'
        middle_right = f'({abstract_boundary(b)}) + ({abstract_boundary(common)})'
        lines += [f'  have combine {binders} (h : {premise}) : {equation} := by', '    calc', f'      _ = {middle_left} := by (try simp only [Nat.two_mul, Nat.add_zero, Nat.zero_add]) <;> ac_rfl', f'      _ = {middle_right} := by rw [h]', '      _ = _ := by (try simp only [Nat.two_mul, Nat.add_zero, Nat.zero_add]) <;> ac_rfl', '  exact combine ' + ' '.join((f'({atom(t)})' for t in terms)) + f' (column_{w} s i)', '']
    lines += ['end ArrayTree', '']
    write(output / f'Columns{batch:03}.lean', '\n'.join(lines))
lines = [f'import Proofs.ArrayTree.Columns{k:03}' for k in range(9)] + ['import Proofs.ColumnSum', '', 'namespace ArrayTree', 'open nArrayMulDataModule', 'set_option linter.unusedVariables false', '', 'def inputPrefix0 (_s : State) (_i : Inputs) : Nat := 0', 'def outputPrefix0 (_s : State) (_i : Inputs) : Nat := 0', 'theorem prefix_0 (s : State) (i : Inputs) : inputPrefix0 s i = outputPrefix0 s i + 1 * 0 := rfl', '']
for w in range(130):
    for label in ['input', 'output']:
        lines += [f'def {label}Prefix{w + 1} (s : State) (i : Inputs) : Nat :=', f'  {label}Prefix{w} s i + {2 ** w} * {label}Column{w} s i', '']
    previous = f'(carryColumn{w - 1} s i)' if w else '0'
    lines += [f'theorem prefix_{w + 1} (s : State) (i : Inputs) :', f'    inputPrefix{w + 1} s i = outputPrefix{w + 1} s i + {2 ** (w + 1)} * carryColumn{w} s i := by', f'  exact ColumnSum.extend {2 ** w} (inputPrefix{w} s i) (outputPrefix{w} s i)', f'    (inputColumn{w} s i) (outputColumn{w} s i) {previous} (carryColumn{w} s i)', f'    (prefix_{w} s i) (boundary_{w} s i)', '']
lines += ['/-- The complete inter-stage compressor preserves its weighted sum,', 'with only the carry beyond bit 129 discarded. -/', 'theorem weighted_sum (s : State) (i : Inputs) :', '    inputPrefix130 s i = outputPrefix130 s i + 2^130 * carryColumn129 s i :=', '  prefix_130 s i', '', 'theorem weighted_sum_modulo (s : State) (i : Inputs) :', '    BitVec.ofNat 130 (inputPrefix130 s i) =', '      BitVec.ofNat 130 (outputPrefix130 s i) := by', '  rw [weighted_sum, BitVec.ofNat_add, BitVec.ofNat_mul]', '  have zero : BitVec.ofNat 130 (2^130) = 0#130 := by decide', '  rw [zero, BitVec.zero_mul, BitVec.add_zero]', '', 'end ArrayTree', '']
write(root / 'lean/Proofs/ArrayTree.lean', '\n'.join(lines))
print(f'Generated {len(chosen)} local exact identities and 130 column conservation proofs')
