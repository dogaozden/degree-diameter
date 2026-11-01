# Build the 3-ball A-coverage bitsets of every B-vertex of the (16,5) graph G (n=33792).
import numpy as np, sys, time
EDGES = '/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges'
t0 = time.time()
with open(EDGES) as f:
    n = int(f.readline())
    E = np.loadtxt(f, dtype=np.int64)
nA = n // 2
adj = np.full((n, 16), -1, dtype=np.int64)
deg = np.zeros(n, dtype=np.int64)
for u, v in E:
    adj[u, deg[u]] = v; deg[u] += 1
    adj[v, deg[v]] = u; deg[v] += 1
assert (deg == 16).all(), 'not 16-regular'
# verify the Z22 shift g -> g+1 is an automorphism (sanity of the symmetry used in this card)
def shift(v, t=1):
    if v < nA:
        blk, x = divmod(v, 256); i, g = divmod(blk, 22)
        return (i * 22 + (g + t) % 22) * 256 + x
    w = v - nA; blk, y = divmod(w, 256); j, h = divmod(blk, 22)
    return nA + (j * 22 + (h + t) % 22) * 256 + y
S = np.array([shift(v) for v in range(n)])
Eset = set(map(tuple, np.sort(E, axis=1).tolist()))
Es = np.sort(S[E], axis=1)
ok = all(tuple(e) in Eset for e in Es.tolist())
print('shift automorphism ok:', ok, flush=True)
# A-coverage bitsets of each B-vertex within distance 3 (B -> A -> B -> A)
W = nA // 8
balls = np.zeros((n - nA, W), dtype=np.uint8)
sizes = np.zeros(n - nA, dtype=np.int64)
for b in range(nA, n):
    N1 = adj[b]
    N2 = np.unique(adj[N1].ravel())
    N3 = np.unique(adj[N2].ravel())
    assert N3.max() < nA
    m = np.zeros(nA, dtype=bool); m[N3] = True
    balls[b - nA] = np.packbits(m, bitorder='little')
    sizes[b - nA] = len(N3)
np.save('/home/user/degree-diameter/research/squads/beyond-small/r1/c02/ball3B.npy', balls)
np.save('/home/user/degree-diameter/research/squads/beyond-small/r1/c02/ball3B_sizes.npy', sizes)
print('ball sizes min/mean/max', sizes.min(), sizes.mean(), sizes.max(), 'time', round(time.time()-t0,1), flush=True)
