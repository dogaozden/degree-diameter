"""Orbits of SL(3,q) (acting as x -> (g u | x3 | g^-T w)) on points, lines and flags of H(q), q prime."""
import sys, numpy as np
from hexlib import load
q = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
N, LP, PL, coord = load(q)
X = coord.astype(np.int64)
P7 = q ** np.arange(7, dtype=np.int64)
codes = (X * P7).sum(1)
order = np.argsort(codes); assert (order == np.arange(N)).all()  # ids are sorted by code
inv = np.array([0] + [pow(a, q - 2, q) for a in range(1, q)])
def normalize(V):
    V = V % q
    first = np.argmax(V != 0, axis=1)
    lead = V[np.arange(len(V)), first]
    return (V * inv[lead][:, None]) % q
def lookup(V):
    c = (normalize(V) * P7).sum(1)
    idx = np.searchsorted(codes, c); assert (codes[idx] == c).all()
    return idx
def act(g, V):
    gi = np.round(np.linalg.inv(g) * np.linalg.det(g)).astype(np.int64)  # adjugate
    det = int(round(np.linalg.det(g))) % q
    ginv = (gi * pow(det, q - 2, q)) % q
    W = np.empty_like(V)
    W[:, 0:3] = (V[:, 0:3] @ g.T) % q
    W[:, 3] = V[:, 3]
    W[:, 4:7] = (V[:, 4:7] @ ginv) % q     # g^{-T} w  (row vector times g^{-1})
    return W
rng = np.random.default_rng(seed)
def rand_sl3():
    while True:
        g = rng.integers(0, q, (3, 3))
        d = int(round(np.linalg.det(g))) % q
        if d:
            g[0] = (g[0] * pow(d, q - 2, q)) % q
            return g
gens = [rand_sl3() for _ in range(2)]
# point permutations
perms = [lookup(act(g, X)) for g in gens]
# check lines map to lines: image of each line's point set must be a line
lineset = {tuple(sorted(r)): i for i, r in enumerate(LP.tolist())}
lperms = []
for pp in perms:
    img = np.sort(pp[LP], axis=1)
    lp = np.array([lineset.get(tuple(r), -1) for r in img.tolist()])
    assert (lp >= 0).all(), 'not an automorphism'
    lperms.append(lp)
print('generators are automorphisms of H(q)')
def orbits(perm_list, n):
    parent = np.arange(n)
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]; a = parent[a]
        return a
    for p in perm_list:
        for a in range(n):
            ra, rb = find(a), find(int(p[a]))
            if ra != rb: parent[ra] = rb
    roots = np.array([find(a) for a in range(n)])
    return roots
pr = orbits(perms, N); lr = orbits(lperms, N)
up, cp = np.unique(pr, return_counts=True); ul, cl = np.unique(lr, return_counts=True)
print('point orbits', sorted(cp.tolist())); print('line orbits', sorted(cl.tolist()))
np.savez('runs/sl3_orbits_q%d.npz' % q, pr=pr, lr=lr, perms=np.array(perms), lperms=np.array(lperms))
