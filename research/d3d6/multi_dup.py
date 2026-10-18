"""k random +2 gadgets at Delta=q+3, then twins by local search. python3 multi_dup.py q k trials seed secs"""
import json, random, sys
from multi_gadget import C, lib, HERE, gadget_incidences, to_graph, random_frame
from dup_ls import ls_side
from dup_ilp import twin

q, k, trials, seed, secs = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5])
rng = random.Random(seed); points, lines = C.pg_plane(q); Delta = q + 3; best = 0
for t in range(trials):
    frames = [random_frame(points, lines, rng) for _ in range(k)]
    inc = gadget_incidences(lines, frames)
    pts = sorted({a for a, b in inc}, key=str); lns = sorted({b for a, b in inc}, key=str)
    ids = {v: i for i, v in enumerate(pts + lns)}; n = len(ids)
    edges = sorted((ids[a], ids[b]) for a, b in inc)
    if lib.max_degree(n, edges) > Delta or not lib.is_valid(n, edges, Delta, 3):
        continue
    side = [0] * len(pts) + [1] * len(lns)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v); adj[v].append(u)
    deg = [len(a) for a in adj]; mult = {}; got = []
    for which in (0, 1):
        s, m = ls_side(adj, deg, side, which, Delta, secs, 1, rng); mult.update(m); got.append(s)
    N, E = twin(n, edges, mult)
    print(f'trial {t}: base {n} twins {got} -> {N}', flush=True)
    if N > best and lib.is_valid(N, E, Delta, 3):
        best = N
        (HERE / 'graphs' / f'multidup_q{q}_k{k}_n{N}.json').write_text(json.dumps({'case': f'd{Delta}D3', 'value': N, 'output': [N, E]}))
        json.dump(frames, open(HERE / 'runs' / f'multidup_q{q}_k{k}_n{N}_frames.json', 'w'))
print('best', best)
