"""card c2: anneal only the two bijection-edge voltages (one value per tau-orbit, tau-invariant) with a fixed
structured incidence voltage family (invariant mode). Usage: python3 anneal_bij.py FAM PRM M SEED ITERS T0"""
import sys, math, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/bcd-d8-r1/c2')
import fam as F
from fam import H, N, q
fam_, prm, M, seed, iters, T0 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), float(sys.argv[6])
rng = np.random.default_rng(seed)
# flag voltages from the family (invariant, rep-based); bijections: equivariant, one voltage per orbit each
flag_edges = F.build(fam_, M, seed, prm, True)[:N * (q + 1)]
brng = np.random.default_rng(seed + 1000)
sigs = [F.hs.equivariant_bijection(H, brng) for _ in range(2)]
NO = len(H.prep)
a = [brng.integers(0, M, NO) for _ in range(2)]
def edges_of(a):
    e = list(flag_edges)
    for j in range(2):
        e += [(p, N + sigs[j][p], int(a[j][H.porb[p]])) for p in range(N)]
    return e
spec = f'/home/user/degree-diameter/research/squads/bcd-d8-r1/c2/ann_{fam_}_p{prm}_M{M}_s{seed}.spec'
def score(a):
    F.hs.write_spec(spec, H, M, edges_of(a), tau_invariant=True)
    return F.hs.bcd_cost(spec, 8, 8)
cur = score(a); best = cur; besta = [x.copy() for x in a]
print('start', cur, flush=True)
for it in range(iters):
    T = T0 * (1 - it / iters) + 1e-9
    j = int(rng.integers(0, 2)); o = int(rng.integers(0, NO)); old = a[j][o]
    a[j][o] = int(rng.integers(0, M))
    c = score(a)
    if c <= cur or rng.random() < math.exp(-(c - cur) / T):
        cur = c
        if c < best:
            best = c; besta = [x.copy() for x in a]
            if best == 0: break
    else:
        a[j][o] = old
    if it % 50 == 0: print('it', it, 'cur', cur, 'best', best, flush=True)
print('BEST', best, 'M', M, 'fam', fam_, prm, 'seed', seed, flush=True)
np.save(f'/home/user/degree-diameter/research/squads/bcd-d8-r1/c2/ann_{fam_}_p{prm}_M{M}_s{seed}_best.npy', np.array(besta))
