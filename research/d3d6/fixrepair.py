"""Build gadgets from a kframe file even if some vertex is overloaded: drop edges at overloaded vertices
(choosing the drop that leaves the fewest far pairs), then add repair edges.  python3 fixrepair.py q frames.txt tag"""
import json, sys
from singer import singer_plane
from multi_gadget import lib, HERE, gadget_incidences
from repair import repair, dist_matrix

q = int(sys.argv[1]); tag = sys.argv[3]
points, lines = singer_plane(q); Delta = q + 3
frs = []
for row in open(sys.argv[2]):
    v = list(map(int, row.split())); A, ell, X = v[0], v[1], v[2:]
    P = next(p for p in sorted(lines[ell]) if p not in X); frs.append((A, ell, P, X))
inc = gadget_incidences(lines, frs)
pts = sorted({a for a, b in inc}, key=str); lns = sorted({b for a, b in inc}, key=str)
V = pts + lns; ids = {v: i for i, v in enumerate(V)}; N = len(ids)
E = {(ids[a], ids[b]) for a, b in inc}; side = [0] * len(pts) + [1] * len(lns)
def far_count(E):
    adj = [[] for _ in range(N)]
    for a, b in E: adj[a].append(b); adj[b].append(a)
    Dm = dist_matrix(N, adj)
    return sum(1 for u in range(N) for v in range(u + 1, N) if Dm[u][v] > 3)
while True:
    deg = [0] * N
    for a, b in E: deg[a] += 1; deg[b] += 1
    over = [u for u in range(N) if deg[u] > Delta]
    if not over: break
    u = over[0]; cand = [e for e in E if u in e]
    best = min(cand, key=lambda e: far_count(E - {e}))
    print('overloaded', V[u], 'drop', V[best[0]], V[best[1]], flush=True)
    E = E - {best}
E2 = repair(N, sorted(E), side, Delta, 3, verbose=True)
ok = E2 is not None and lib.is_valid(N, E2, Delta, 3)
print('n', N, 'valid', ok)
if ok:
    out = HERE / 'graphs' / f'{tag}_q{q}_d{Delta}_n{N}.json'
    out.write_text(json.dumps({'case': f'd{Delta}D3', 'value': N, 'output': [N, E2]})); print('wrote', out)
    json.dump(frs, open(HERE / 'runs' / f'{tag}_q{q}_frames.json', 'w'))
