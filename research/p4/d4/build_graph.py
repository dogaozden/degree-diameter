"""Build the Theorem B graph (dual form) from a stand-in set M of W(3,q) points, and check it.

Vertices: W(3,q) points, W(3,q) lines, one copy s' of every spread line (adjacent to the q+1 points of s),
and one copy m' of every m in M (adjacent to the q+1 t.i. lines through m, except that the spread line through m is
replaced by its copy s' when the original s already serves another copy). Dually this is Q(4,q) + one copy of the
elliptic-quadric ovoid + |M| line copies with stand-ins. Max degree q+2, diameter 4 (Theorem B).

usage: python3 build_graph.py SOLUTION.json [OUT.json]    (SOLUTION has keys q and M, K^2 model of w3k.py)
"""
import json
import sys
from pathlib import Path

from w3k import W3

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'problems' / 'bipartite_dd'))
import lib  # noqa: E402

d = json.loads(Path(sys.argv[1]).read_text())
q, M = d['q'], d['M']
model = d.get('model', 'K')
if model == 'K':
    W = W3(q)
else:
    from w3f import W3F
    W = W3F(q, d['e'])
n = len(W.pts)
nl = len(W.lines)
line_id = {L: j for j, L in enumerate(W.lines)}
on = [[] for _ in range(n)]
for j, L in enumerate(W.lines):
    for p in L:
        on[p].append(j)
edges = [(p, n + j) for j, L in enumerate(W.lines) for p in L]
v = n + nl
scopy = {}
for L in W.spread:
    scopy[line_id[L]] = v
    edges += [(p, v) for p in L]
    v += 1
used = set()
for m in M:
    y = v
    v += 1
    for j in on[m]:
        stand = n + j
        if W.is_spread_line[j] and stand in used:
            stand = scopy[j]
        assert stand not in used, 'M violates the stand-in capacities'
        used.add(stand)
        edges.append((y, stand))
N = v
ok = lib.is_valid(N, edges, q + 2, 4)
print(f'q={q} |M|={len(M)} order={N} edges={len(edges)} valid={ok}')
if len(sys.argv) > 2 and ok:
    Path(sys.argv[2]).write_text(json.dumps({'case': f'd{q + 2}D4', 'value': N, 'output': [N, [list(e) for e in edges]]}))
    print('wrote', sys.argv[2])
