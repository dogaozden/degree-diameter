"""Local search for the hub graph Y of the all-H construction (allH.py) over W(q).
Y = bipartite (q-r)-regular graph between B-hubs and A-hubs, kept regular by edge switches.
Objective: number of unordered vertex pairs at distance > 5 (computed by boolean powers of I+A).
usage: python3 hubsearch.py q r iters seed
Writes edges_q{q}_r{r}.txt and runs apsp when the objective reaches 0."""
import sys, os, math, random, time
os.environ.setdefault("OMP_NUM_THREADS", "1"); os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib, levels
from duality import duality, OUT

q, r, iters, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rng = random.Random(seed)
G, phi_pt, phi_line = duality(q)
F = G.F
a = next(a for a in range(q) if all(F.add[F.add[F.mul[x][x]][x]][a] != 0 for x in range(q)))
def Qf(v):
    s = F.add[F.mul[v[0]][v[2]]][F.mul[v[1]][v[1]]]
    s = F.add[s][F.mul[v[1]][v[3]]]
    return F.add[s][F.mul[a][F.mul[v[3]][v[3]]]]
O = [i for i, v in enumerate(G.coords) if Qf(v) == 0]
assert len(O) == q * q + 1 and gqlib.is_partial_ovoid(G, O)
n_lev = 2 * r + 1
types = ['H'] * n_lev
trans = [(j, k) for j in range(n_lev) for k in range(1, r + 1)]
M = {t: list(phi_pt) for t in trans}
R = {t: set(O) for t in trans}
Bhubs = [[(j, x, (j, k)) for j in range(n_lev)] for x in O for k in range(1, r + 1)]
Ahubs = [[(j, phi_pt[x], ((j - k) % n_lev, k)) for j in range(n_lev)] for x in O for k in range(1, r + 1)]
K = len(Bhubs); dY = q - r; d = q + 1 + r
n0, base_edges = levels.build(G, types, M, R, Bhubs, Ahubs, [])
nv = n_lev * (G.np + G.nl)
N = n0
B0 = np.zeros((N, N), dtype=np.float32)
for a_, b_ in base_edges:
    B0[a_, b_] = 1; B0[b_, a_] = 1
I = np.eye(N, dtype=np.float32)

HUBS = list(range(nv, N))

def bad_pairs(Y):
    # number of (hub, vertex) pairs at distance > 5; only hub rows are propagated (cheap)
    A = B0.copy()
    for h, g in Y:
        A[nv + h, nv + K + g] = 1; A[nv + K + g, nv + h] = 1
    V = I[HUBS].copy()
    for _ in range(5):
        V = np.minimum(V + V @ A, 1.0)
    return int(np.count_nonzero(V == 0))

def random_Y():
    # union of dY edge-disjoint random perfect matchings (simple, (q-r)-regular)
    Y = set()
    for _ in range(dY):
        while True:
            perm = list(range(K)); rng.shuffle(perm)
            new = {(h, perm[h]) for h in range(K)}
            if not (new & Y):
                Y |= new
                break
    return sorted(Y)

def switch(Y):
    Y = list(Y)
    for _ in range(1000):
        i, j = rng.sample(range(len(Y)), 2)
        (h1, g1), (h2, g2) = Y[i], Y[j]
        if h1 == h2 or g1 == g2:
            continue
        if (h1, g2) in Y or (h2, g1) in Y:
            continue
        Y[i] = (h1, g2); Y[j] = (h2, g1)
        return Y
    return Y

Y = random_Y()
f = bad_pairs(Y)
best = (f, list(Y))
T0 = 2.0
t0 = time.time()
print('start f=%d' % f, flush=True)
for it in range(iters):
    if f == 0:
        break
    T = T0 * (1 - it / iters) + 0.05
    Y2 = switch(Y)
    f2 = bad_pairs(Y2)
    if f2 <= f or rng.random() < math.exp(-(f2 - f) / T):
        Y, f = Y2, f2
        if f < best[0]:
            best = (f, list(Y))
            print('it %d f=%d best' % (it, f), round(time.time() - t0, 1), flush=True)
    if it % 100 == 0:
        print('it %d f=%d best=%d t=%.0f' % (it, f, best[0], time.time() - t0), flush=True)
f, Y = best
print('final best f=%d' % f, flush=True)
n, edges = levels.build(G, types, M, R, Bhubs, Ahubs, sorted(Y))
final = os.path.join(OUT, 'edges_q%d_r%d.txt' % (q, r))
levels.write_edges(final, n, edges)
out = levels.apsp(final, d, 5)
print('apsp:', out, 'file', final, flush=True)
