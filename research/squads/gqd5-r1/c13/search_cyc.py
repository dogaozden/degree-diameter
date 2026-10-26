"""Hill-climb the line bijections of cyc.py layout to minimise ordered pairs at distance > 5.
Usage: search_cyc.py L seed iters out.txt"""
import sys, random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib
L, seed, iters, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
G = gqlib.Q5(2)
P, N = G.np, G.nl
per = P + N
n = L * per
rng = random.Random(seed)
base = np.zeros((n, n), dtype=bool)
for j in range(L):
    b = j * per
    for l, pts in enumerate(G.lines):
        for p in pts:
            base[b + p, b + P + l] = base[b + P + l, b + p] = True
perms = [rng.sample(range(N), N) for _ in range(L)]   # perms[j]: line l of level j -> line of level j+1

def build(perms):
    A = base.copy()
    for j in range(L):
        j2 = (j + 1) % L
        for l in range(N):
            u = j * per + P + l; v = j2 * per + P + perms[j][l]
            A[u, v] = A[v, u] = True
    return A

def bad(A):
    R = np.eye(n, dtype=bool); cur = R.copy()
    Ai = A.astype(np.float32)
    reach = R.astype(np.float32)
    step = R.astype(np.float32)
    cum = R.copy()
    for _ in range(5):
        step = ((step @ Ai) > 0).astype(np.float32)
        cum |= step > 0
    return int((~cum).sum())

A = build(perms); cur = bad(A)
print('start bad', cur, flush=True)
for it in range(iters):
    j = rng.randrange(L); a, b = rng.sample(range(N), 2)
    perms[j][a], perms[j][b] = perms[j][b], perms[j][a]
    A2 = build(perms); v = bad(A2)
    if v <= cur:
        cur = v
        if v == 0:
            break
    else:
        perms[j][a], perms[j][b] = perms[j][b], perms[j][a]
    if it % 200 == 0:
        print(it, cur, flush=True)
print('final bad', cur, flush=True)
with open(out, 'w') as f:
    f.write('%d\n' % n)
    ed = [(u, v) for u in range(n) for v in range(u + 1, n) if A[u, v]] if cur == 0 else []
    for u, v in ed: f.write('%d %d\n' % (u, v))
