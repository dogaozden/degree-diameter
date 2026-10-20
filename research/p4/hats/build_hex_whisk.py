"""Delorme's levels on H(q) plus a whisker file -> graph JSON in graphs/, checked with lib.is_valid.

python3 build_hex_whisk.py whiskers_ansatz_q{q}.json
"""
import json
import sys
import importlib.util
from pathlib import Path

from lift import ROOT, lib

spec = importlib.util.spec_from_file_location('d6lift', ROOT / 'research' / 'p4' / 'd6' / 'lift.py')
d6lift = importlib.util.module_from_spec(spec)
spec.loader.exec_module(d6lift)
HERE = Path(__file__).resolve().parent
d = json.loads(Path(sys.argv[1]).read_text())
q, S, v, W = d['q'], d['S'], d['v'], d['whiskers']
lines = json.loads((ROOT / 'research' / 'gh6' / 'hex' / f'hexagon_q{q}.json').read_text())['lines']
N = len(lines)
through = [[] for _ in range(N)]
for k, L in enumerate(lines):
    for p in L:
        through[p].append(k)
adj = [list(N + k for k in through[p]) for p in range(N)] + [list(L) for L in lines]
lev = [-1] * (2 * N)
for s in S:
    if s != v:
        lev[N + s] = 1
        for p in lines[s]:
            lev[p] = 0
lev[N + v] = 2
for p in lines[v]:
    lev[p] = 1
    for k in through[p]:
        if k != v:
            lev[N + k] = 0
assert len(set(W)) == len(W)
for k in W:
    assert lev[N + k] == -1
    lev[N + k] = 0
ex = d6lift.degree_excess(adj, lev)
print('q', q, 'whiskers', len(W), 'max excess', max(ex), 'gain', d6lift.gain(lev))
n, edges, _ = d6lift.build(2 * N, adj, lev)
ok = lib.is_valid(n, edges, q + 2, 6)
print('order', n, 'valid(lib)', ok, flush=True)
if ok:
    out = HERE / 'graphs' / f'hex_q{q}_delorme_whisk{len(W)}_n{n}.json'
    out.write_text(json.dumps({'case': f'd{q+2}D6', 'value': n, 'output': [n, [list(e) for e in edges]]}))
    print('wrote', out)
