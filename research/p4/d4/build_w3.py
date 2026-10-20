"""Corollary B1 graph from a weighted 3-ovoid w of W(3,q): W(3,q) incidence graph + 3 copies of every spread line
+ w(m) copies of every point m (adjacent to the t.i. lines through m). Dually: Q(4,q) + 3 ovoid copies + a weighted
3-cover by lines. (q+4)-regular, order 2(q^2+1)(q+4).  usage: build_w3.py SOL.json [OUT.json]"""
import json, sys
from pathlib import Path
from w3k import W3
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'problems' / 'bipartite_dd'))
import lib
d = json.loads(Path(sys.argv[1]).read_text()); q, w = d['q'], d['w']
W = W3(q); n = len(W.pts); nl = len(W.lines)
edges = [(p, n + j) for j, L in enumerate(W.lines) for p in L]
v = n + nl
for L in W.spread:
    for _ in range(3):
        edges += [(p, v) for p in L]; v += 1
for m in range(n):
    for _ in range(w[m]):
        edges += [(v, n + j) for j in W.on[m]]; v += 1
ok = lib.is_valid(v, edges, q + 4, 4)
print(f'q={q} order={v} expected={2*(q*q+1)*(q+4)} valid={ok}')
if ok and len(sys.argv) > 2:
    Path(sys.argv[2]).write_text(json.dumps({'case': f'd{q+4}D4', 'value': v, 'output': [v, [list(e) for e in edges]]}))
