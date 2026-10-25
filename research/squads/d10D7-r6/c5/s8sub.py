"""Subgroups of S8 = W(A7) inside W(E7) mod q: sigma -> product of simple reflections (A7 base), orbits on points."""
import sys, time, numpy as np, pickle, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r6/c5')
from grp5 import *
from sub5 import clique_exact
from common5 import orbits_from_perms, orbit_info
q = 5
w = W(q)
base = w.dynkin([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6)], 7, seed=1, tries=200)   # A7 chain, rows = roots
Rm = [np.array(w.G.C) for _ in []]
def refl_mat(v):
    v = np.asarray(v, dtype=np.int64)
    # x -> x - B(x,v) v  as 7x7 matrix acting on column vectors: M = I - v (A v)^T  (B(x,v) = x^T A v)
    return (np.eye(7, dtype=np.int64) - np.outer(v, (A7 @ v) % q)) % q
RM = [refl_mat(b) for b in base]
for M in RM: assert w.G.is_isometry(M)
def mat_of_perm8(sig):
    sig = list(sig); word = []
    while True:
        d = [i for i in range(7) if sig[i] > sig[i + 1]]
        if not d: break
        i = d[0]; sig[i], sig[i + 1] = sig[i + 1], sig[i]; word.append(i)
    M = np.eye(7, dtype=np.int64)
    for i in word: M = (M @ RM[i]) % q
    return M
def perm_mat_check():
    # verify: transposition (i,i+1) -> RM[i] and consistency of the homomorphism on random pairs
    import random
    rng = random.Random(0)
    for _ in range(20):
        s = list(range(8)); rng.shuffle(s); t = list(range(8)); rng.shuffle(t)
        st = [s[t[k]] for k in range(8)]
        # not checking group law precisely; just that matrices are isometries
        assert w.G.is_isometry(mat_of_perm8(s))
perm_mat_check()
def perm_of_s8(sig):
    M = mat_of_perm8(sig)
    return w.G.perm_of_matrix(M)
# permutation generators of subgroups of S8 on 8 letters
def cyc(*cycles):
    p = list(range(8))
    for c in cycles:
        for a, b in zip(c, c[1:] + c[:1]): p[a] = b
    return p
def gens_for(name):
    if name == 'S8': return [cyc((0,1)), cyc((0,1,2,3,4,5,6,7))]
    if name == 'A8': return [cyc((0,1,2)), cyc((0,1,2,3,4,5,6,7)) if False else cyc((1,2,3,4,5,6,7))]
    if name == 'S7': return [cyc((0,1)), cyc((0,1,2,3,4,5,6))]
    if name == 'S6xS2': return [cyc((0,1)), cyc((0,1,2,3,4,5)), cyc((6,7))]
    if name == 'PGL27':
        # points of PG(1,7) = {0..6, inf=7}: x->x+1, x->3x, x->-1/x
        inv = lambda x: 7 if x == 0 else (pow(x, 5, 7) * (-1) % 7 if x != 7 else 0)
        f1 = [ (x + 1) % 7 if x < 7 else 7 for x in range(8)]
        f2 = [ (3 * x) % 7 if x < 7 else 7 for x in range(8)]
        f3 = [ 7 if x == 0 else (0 if x == 7 else (( -pow(x, 5, 7)) % 7)) for x in range(8)]
        return [f1, f2, f3]
    if name == 'AGL32':
        # points GF(2)^3 = {0..7} as bit vectors; translations and GL(3,2) generators
        t1 = [x ^ 1 for x in range(8)]
        t2 = [x ^ 2 for x in range(8)]
        t3 = [x ^ 4 for x in range(8)]
        def lin(M):
            out = []
            for x in range(8):
                y = 0
                for i in range(3):
                    if (x >> i) & 1: y ^= M[i]
                out.append(y)
            return out
        g1 = lin([1, 2 | 4, 4]) ; g2 = lin([2, 4, 1 | 2 | 4]) ; g3 = lin([2, 4, 1])
        return [t1, t2, t3, g1, g2, g3]
    if name == 'S4wrS2': return [cyc((0,1)), cyc((0,1,2,3)), cyc((0,4),(1,5),(2,6),(3,7))]
    if name == 'S2wrS4': return [cyc((0,1)), cyc((2,3)), cyc((4,5)), cyc((6,7)), cyc((0,2),(1,3),(4,6),(5,7)), cyc((0,4),(1,5),(2,6),(3,7))]
    if name == 'S4xS4': return [cyc((0,1)), cyc((0,1,2,3)), cyc((4,5)), cyc((4,5,6,7))]
    if name == 'AGL13': return [cyc((0,1,2,3,4,5,6)), cyc((0,1)), cyc((1,2))]
    if name == 'S5xS3': return [cyc((0,1)), cyc((0,1,2,3,4)), cyc((5,6)), cyc((5,6,7))]
    if name == 'Z8': return [cyc((0,1,2,3,4,5,6,7))]
    if name == 'Z3': return [cyc((0,1,2))]
    if name == 'S3': return [cyc((0,1,2)), cyc((0,1))]
    if name == 'Z2x4': return [cyc((0,1),(2,3),(4,5),(6,7))]
    if name == 'Z4': return [cyc((0,1,2,3),(4,5,6,7))]
    if name == '2^4:A6?': return [cyc((0,1)), cyc((0,1,2,3,4,5,6,7)), cyc((2,3))]
    raise KeyError(name)
if __name__ == '__main__':
    names = sys.argv[1:]
    res = {}
    for name in names:
        t = time.time()
        gens = gens_for(name)
        perms = [perm_of_s8(g) for g in gens]
        lab = orbits_from_perms(w.G.N, perms)
        members, S, M = orbit_info(w.G, lab)
        sizes = np.bincount(lab)
        print(name, 'orbits', len(sizes), 'sc', len(S), 'sizes', sorted(set(sizes.tolist()))[:12], flush=True)
        if len(S) == 0: continue
        wgt, cl, tt = clique_exact(sizes, S, M, tlimit=120)
        pts = sorted(int(p) for o in cl for p in members[o])
        print(name, 'max weight clique', wgt, 'time', round(tt, 2), 'orbits', len(cl), flush=True)
        res[name] = (wgt, pts)
    pickle.dump(res, open('/home/user/degree-diameter/research/squads/d10D7-r6/c5/s8_res.pkl', 'wb'))
