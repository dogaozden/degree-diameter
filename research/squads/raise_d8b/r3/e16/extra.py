import sys, random
from collections import deque
# usage: extra.py BASE_EDGES K_LINE K_POINT SEED OUT_EDGES
base, KL, KP, seed, outf = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
M = int(sys.argv[6]) if len(sys.argv) > 6 else 1
random.seed(seed)
lines = open(base).read().split('\n')
n = int(lines[0]); E = [tuple(map(int, s.split())) for s in lines[1:] if s.strip()]
N2 = 2 * 3906; NV0 = 3 * N2                       # levels: 3 levels, 2N vertices each; hubs after
LH0, PH0 = NV0, NV0 + 81                           # 81 line-side hubs then 81 point-side hubs
adj = [[] for _ in range(n)]
for a, b in E: adj[a].append(b); adj[b].append(a)
deg = [len(x) for x in adj]
# bipartition colouring
col = [-1] * n; col[0] = 0; dq = deque([0])
while dq:
    x = dq.popleft()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1 - col[x]; dq.append(y)
hubadj = lambda h: [y for y in adj[h]]
cL = max(set(col[y] for y in adj[LH0]), key=lambda c: sum(1 for z in range(LH0, LH0+81) for y in adj[z] if col[y]==c))
cP = 1 - cL
used_hub = set(y for h in range(NV0, n) for y in adj[h])
def cands(color, levels):
    out = {}
    for v in range(NV0):
        if deg[v] == 6 and v not in used_hub and col[v] == color and (v // N2) in levels:
            out.setdefault(v // N2, []).append(v)
    return out
cl = cands(cL, (1, 2)); cp = cands(cP, (0, 2))
print('line-side candidates per level', {k: len(v) for k, v in cl.items()}, 'point-side', {k: len(v) for k, v in cp.items()})
new = []   # (hub vertex, neighbours)
taken = set()
nv = n
def pick(pool_by_level, levels):
    out = []
    for j in levels:
        for _ in range(M):
            pool = [v for v in pool_by_level.get(j, []) if v not in taken]
            if not pool: return None
            v = random.choice(pool); taken.add(v); out.append(v)
    return out
for _ in range(KL):
    nb = pick(cl, (1, 2))
    if nb is None: break
    new.append((nv, nb)); nv += 1
for _ in range(KP):
    nb = pick(cp, (0, 2))
    if nb is None: break
    new.append((nv, nb)); nv += 1
newE = [(h, u) for h, nb in new for u in nb]
import os
PAIR = int(os.environ.get('PAIR', '0'))
if PAIR:
    # join line-side extra hub i to point-side extra hub i (one hub-graph edge each, while degrees allow)
    lin = [h for h, nb in new if len(nb) == 2 * M and h >= n + 0 and h < n + KL]
    pnt = [h for h, nb in new if h >= n + KL]
    for a, b in zip(lin, pnt):
        newE.append((a, b))
print('pairs', len([1 for _ in newE]))
print('extra hubs added', len(new), 'new n', nv, 'extra edges', len(newE))
with open(outf, 'w') as f:
    f.write(f'{nv}\n')
    for a, b in E + newE: f.write(f'{a} {b}\n')
