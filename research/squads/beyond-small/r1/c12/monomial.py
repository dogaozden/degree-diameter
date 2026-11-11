# Enumerate monomial (+Frobenius) collineations of H(q) in the Q(6,q) model, dedupe, report fixed-point-free ones.
import sys, itertools, pickle, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond-small/r1/c12')
from hexlib import Hex, fixed_free

q = int(sys.argv[1]); path = f'hex/hex_q{q}.bin'
hx = Hex(path)
t0 = time.time()
ident = np.arange(7)
pairs = [(0, 4), (1, 5), (2, 6)]
# sigma: permutations of coordinates preserving the pairing {0,4},{1,5},{2,6} and fixing 3
perms = []
for pp in itertools.permutations(range(3)):
    for sw in itertools.product([0, 1], repeat=3):
        sig = np.arange(7)
        for k, (a, b) in enumerate(pairs):
            na, nb = pairs[pp[k]]
            if sw[k]: na, nb = nb, na
            sig[a], sig[b] = na, nb
        perms.append(sig)
F = range(1, q)
cands = []
for sig in perms:
    for lam in range(1, q):
        # d3^2 = lam
        sq = [x for x in range(1, q) if hx.MUL[x, x] == lam]
        for d3 in sq:
            for d0, d1, d2 in itertools.product(F, repeat=3):
                d = np.zeros(7, dtype=np.int64)
                d[0], d[1], d[2], d[3] = d0, d1, d2, d3
                d[4] = hx.MUL[lam, hx.INV[d0]]; d[5] = hx.MUL[lam, hx.INV[d1]]; d[6] = hx.MUL[lam, hx.INV[d2]]
                cands.append((sig, d))
print('monomial candidates', len(cands), flush=True)
found = {}
for sig, d in cands:
    for k in range(hx.e):
        pp = hx.map_points(sig, d, k)
        if pp is None: continue
        key = pp.tobytes()
        if key in found: continue
        lp = hx.line_perm(pp)
        if lp is None: continue
        found[key] = (pp, lp, (tuple(sig), tuple(d), k))
print('collineations found (distinct point perms):', len(found), 'time %.1f' % (time.time() - t0), flush=True)
elems = list(found.values())
# freeness
fpf = [e for e in elems if fixed_free(e[0], e[1]) and not np.array_equal(e[0], np.arange(hx.N))]
print('fixed-point-free nonidentity elements:', len(fpf), flush=True)
with open(f'monomial_q{q}.pkl', 'wb') as f:
    pickle.dump([(e[0].astype(np.int32), e[1].astype(np.int32), e[2]) for e in elems], f)
print('saved', len(elems))
