"""Duplication local search on a saved graph: python3 dup_file.py graph.json Delta D [seconds]"""
import json, random, sys
from collections import deque
from dup_ls import ls_side
from dup_ilp import twin, HERE, lib

g = json.load(open(sys.argv[1])); Delta, D = int(sys.argv[2]), int(sys.argv[3])
secs = float(sys.argv[4]) if len(sys.argv) > 4 else 20
n, edges = g['output']
adj = [[] for _ in range(n)]
for u, v in edges:
    adj[u].append(v); adj[v].append(u)
side = [-1] * n; side[0] = 0; dq = deque([0])
while dq:
    u = dq.popleft()
    for w in adj[u]:
        if side[w] < 0: side[w] = 1 - side[u]; dq.append(w)
deg = [len(a) for a in adj]
rng = random.Random(1); mult = {}
for which in (0, 1):
    s, m = ls_side(adj, deg, side, which, Delta, secs, 1, rng)
    print('side', which, s); mult.update(m)
N, E = twin(n, [tuple(e) for e in edges], mult)
ok = lib.is_valid(N, E, Delta, D)
print(n, '->', N, 'valid', ok)
if ok and N > n:
    out = HERE / 'graphs' / f'dupfile_d{Delta}D{D}_n{N}.json'
    out.write_text(json.dumps({'case': f'd{Delta}D{D}', 'value': N, 'output': [N, E]})); print(out)
