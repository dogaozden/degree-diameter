# Search for non-monomial collineations of the form I + N with N supported on <=2 entries (root-element candidates).
import sys, itertools, pickle, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond-small/r1/c12')
from hexlib import Hex, fixed_free
q = int(sys.argv[1]); hx = Hex(f'hex/hex_q{q}.bin')
pos = [(i, j) for i in range(7) for j in range(7) if i != j]
X = hx.coords
def apply(G):
    # Y = G X over F_q (G is 7x7 ints), then normalize; returns point perm or None
    Y = np.zeros_like(X)
    for i in range(7):
        acc = np.zeros(X.shape[0], dtype=np.int64)
        for j in range(7):
            if G[i, j]:
                acc = hx.ADD[acc, hx.MUL[G[i, j], X[:, j]]]
        Y[:, i] = acc
    Yn = hx.normalize_rows(Y)
    c = Yn @ (q ** np.arange(7, dtype=np.int64))
    idx = np.minimum(np.searchsorted(hx.codes, c), hx.N - 1)
    if not np.all(hx.codes[idx] == c): return None
    return idx
found = []
seen = set()
t0 = time.time()
for r in (1, 2):
    for ps in itertools.combinations(pos, r):
        for vals in itertools.product(range(1, q), repeat=r):
            G = np.eye(7, dtype=np.int64)
            for (i, j), v in zip(ps, vals): G[i, j] = v
            # quick test on a few points before the full check
            pp = apply(G)
            if pp is None: continue
            lp = hx.line_perm(pp)
            if lp is None: continue
            key = pp.tobytes()
            if key in seen: continue
            seen.add(key)
            found.append((pp.astype(np.int32), lp.astype(np.int32), (ps, vals)))
    print('r', r, 'found so far', len(found), 'time %.1f' % (time.time() - t0), flush=True)
nonmono = [f for f in found if f[2][0] and True]
print('total distinct new collineations (I+N, |supp|<=2):', len(found))
for f in found[:10]: print(f[2])
pickle.dump(found, open(f'unip_q{q}.pkl', 'wb'))
