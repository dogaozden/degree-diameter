"""card c2: structured (algebraic) incidence voltages on the H(5) incidence edges, random/annealed bijection voltages.
Usage: python3 fam.py FAMILY M SEED [PARAM] [--inv]  -> prints COST and writes spec c2/<family>_M_seed.spec"""
import sys, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/bigcheck-dist/d8')
import hexspec as hs

H = hs.Hex('/tmp/bcdt/hex/hex_q5.bin', '/tmp/bcdt/hex/singer_q5.bin')
N, q = H.N, H.q
HERE = '/home/user/degree-diameter/research/squads/bcd-d8-r1/c2'

def B(x, y):
    """bilinear form of H(q) (hexlib): x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 mod q"""
    return (x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2*x[3]*y[3]) % q

def flag_value(fam, p, L, prm, M, rng):
    """voltage of flag (point p, line L) as an integer mod M (L = line index 0..N-1)"""
    if fam == 'rand':
        return int(rng.integers(0, M))
    if fam == 'idx':            # position of p in the stored point list of L, times prm
        pos = list(H.lines[L]).index(p)
        return (prm * pos) % M
    if fam == 'bil':            # B(p, c_L) in GF(q), with c_L = point with index L mod N (a fixed reference point)
        c = (L % N)
        val = B(H.coord[p], H.coord[c])
        return (prm * val) % M
    if fam == 'bilidx':         # combination: 6*B + idx labels, index-type and form-type together
        pos = list(H.lines[L]).index(p)
        c = (L % N)
        val = B(H.coord[p], H.coord[c])
        return (prm * val + pos) % M
    if fam == 'zb':             # integer bilinear form over Z_M: sum_i x_i(p) * y_i(c_L), coords as ints 0..4
        c = (L % N)
        x = [int(t) for t in H.coord[p]]; y = [int(t) for t in H.coord[c]]
        s = sum(a * b for a, b in zip(x, y))
        return (prm * s + 0) % M
    if fam == 'pidx':           # product of integer indices (bilinear over Z_M in the indices)
        pos = list(H.lines[L]).index(p)
        return (prm * p * L + pos) % M
    if fam == 'sumL':           # <x(p), sum of coordinates of the points of L> over Z_M
        y = sum(H.coord[r] for r in H.lines[L])
        return (prm * int(np.dot(H.coord[p], y))) % M
    if fam == 'sumLq':          # GF(q)-bilinear value of p with the sum of the points of L, lifted to Z_M, times prm
        y = sum(H.coord[r] for r in H.lines[L])
        return (prm * int(np.dot(H.coord[p], y))) % M
    raise ValueError(fam)

def build(fam, M, seed, prm=1, inv=False, bij_seed=None):
    rng = np.random.default_rng(seed)
    edges = []
    if inv:
        # tau-invariant: flag voltage defined on the orbit representative flag and transported by tau
        w = np.zeros((len(H.prep), q + 1), dtype=np.int64)
        for o, p in enumerate(H.prep):
            for s, L in enumerate(H.plines[p]):
                w[o, s] = flag_value(fam, p, L, prm, M, rng)
        for p in range(N):
            o, e = H.porb[p], H.ppos[p]; r = H.prep[o]
            for L in H.plines[p]:
                L0 = L
                for _ in range((H.KA - e) % H.KA): L0 = H.tl[L0]
                s = list(H.plines[r]).index(L0)
                edges.append((p, N + L, int(w[o, s])))
    else:
        for p in range(N):
            for L in H.plines[p]:
                edges.append((p, N + L, flag_value(fam, p, L, prm, M, rng)))
    brng = np.random.default_rng(bij_seed if bij_seed is not None else seed + 1000)
    for j in range(2):
        sig = hs.equivariant_bijection(H, brng)
        a = brng.integers(0, M, len(H.prep))
        edges += [(p, N + sig[p], int(a[H.porb[p]])) for p in range(N)]
    return edges

if __name__ == '__main__':
    fam, M, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    prm = int(sys.argv[4]) if len(sys.argv) > 4 and not sys.argv[4].startswith('--') else 1
    inv = '--inv' in sys.argv
    edges = build(fam, M, seed, prm, inv)
    spec = f'{HERE}/spec_{fam}_p{prm}_M{M}_s{seed}{"_inv" if inv else ""}.spec'
    hs.write_spec(spec, H, M, edges, tau_invariant=inv)
    cost = hs.bcd_cost(spec, 8, 8)
    print(f'COST {cost} fam={fam} prm={prm} M={M} seed={seed} inv={inv} spec={spec}')
