"""O-partial spreads of Q(4,q) as a maximum independent set: lines conflict when they share a non-ovoid point.
Solved by research/gh6/ils_mis.c (compiled here as ./ils_mis). Builds and checks the doubling graph.

python3 opart_ils.py q SECONDS SEED
"""
import json
import subprocess
import sys
import importlib.util
from pathlib import Path

from lift import ROOT, lib, gq_edges
from gq_clones import q4

spec = importlib.util.spec_from_file_location('d6lift', ROOT / 'research' / 'p4' / 'd6' / 'lift.py')
d6lift = importlib.util.module_from_spec(spec)
spec.loader.exec_module(d6lift)
HERE = Path(__file__).resolve().parent
q, secs, seed = int(sys.argv[1]), sys.argv[2], sys.argv[3]
pts, lines, ovoid = q4(q)
n, m = len(pts), len(lines)
O = set(ovoid)
at = {}
for j, L in enumerate(lines):
    for p in L:
        if p not in O:
            at.setdefault(p, []).append(j)
E = sorted({(a, b) for js in at.values() for a in js for b in js if a < b})
g = HERE / 'runs' / f'opart_conflict_q{q}.txt'
g.parent.mkdir(exist_ok=True)
g.write_text(f'{m} {len(E)}\n' + ''.join(f'{a} {b}\n' for a, b in E))
r = subprocess.run([str(HERE / 'ils_mis'), str(g), secs, seed], capture_output=True, text=True)
M = [int(x) for x in r.stdout.split('\n')[1].split()]
cov = {}
for j in M:
    for p in lines[j]:
        if p not in O:
            assert p not in cov
            cov[p] = j
print(f'q={q}: O-partial spread {len(M)} (Theorem A needs > {q*q - 2*q - 3}; bound q^2-q+2 = {q*q-q+2})', flush=True)
adj = [[] for _ in range(n + m)]
for u, w in gq_edges(n, lines):
    adj[u].append(w)
    adj[w].append(u)
lev = [-1] * (n + m)
for p in O:
    lev[p] = 0
for j in M:
    lev[n + j] = 0
N, H, _ = d6lift.build(n + m, adj, lev)
ok = lib.is_valid(N, H, q + 2, 4)
print(f'order {N} (Theorem A: {2*q*q*(q+2)}), valid {ok}', flush=True)
if ok:
    (HERE / 'graphs' / f'opart_q{q}_n{N}.json').write_text(json.dumps(
        {'case': f'd{q+2}D4', 'value': N, 'output': [N, [list(e) for e in H]], 'lines': M, 'ovoid': sorted(O)}))
