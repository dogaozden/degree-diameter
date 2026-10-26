"""gen8.py: typed-copy dihedral lifts of H(q) for glift (card c8, round r1_d8c).

Group D_n (2n copies): rotations (t=0) = H-copies (points colour 0), reflections (t=1) = D-copies (lines colour 0).
Base graph: points 0..N-1 (colour 0), lines N..2N-1 (colour 1), plus
  - incidence darts p->l with voltage 0 (the hexagon, zero hexagon voltages),
  - type-preserving hop: semi-edge at every base vertex v with reflection voltage (k_v, 1):
      H-copy element (v,(j,0)) ~ D-copy element (v,(j+k_v,1)); involution so one edge per lift vertex,
  - type-changing hop: one matching sigma: point p -> line N+sigma(p) with rotation voltage r_p (same-type copies).
Modes:
  rand        : k_v, r_p uniform in Z_n; sigma uniform among lines not incident to p (derangement-like).
  pencil      : k_v = phi(c_v), r_p = phi(c_p) with pencil coordinate c = [B(a,x):B(a',x)] in PG(1,q) for points,
                and for lines the pencil of the sums over the points on the line; phi(c) = (c*n)//(q+1) + shift.
                sigma uniform among non-incident lines (rand).
  pencil_d3   : as pencil, but sigma(p) a line at distance 3 from p (random among them).
Usage: python3 gen8.py MODE q n seed OUT
Polar form of Tits' quadric X0X4+X1X5+X2X6=X3^2 (q prime only): B(x,y)=x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3.
"""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load, dist_from_point


def B(x, y, p):
    return (x[0]*y[4]+x[4]*y[0]+x[1]*y[5]+x[5]*y[1]+x[2]*y[6]+x[6]*y[2]-2*x[3]*y[3]) % p


def pencil(vals_s, vals_t, p):
    """index in 0..p of [s:t] in PG(1,p); p = infinity."""
    if vals_t % p == 0:
        return p
    return (vals_s * pow(int(vals_t), p - 2, p)) % p


def main():
    mode, q, n, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    out = sys.argv[5]
    rng = np.random.default_rng(seed)
    N, LP, PL, coord = load(q)
    X = coord.astype(np.int64)
    a = np.array([0, 0, 0, 0, 1, 0, 0])      # fixed vectors for the pencil
    a2 = np.array([1, 0, 0, 0, 0, 0, 0])
    if mode == 'pencil' or mode == 'pencil_d3':
        # point classes
        cp = np.zeros(N, dtype=np.int64)
        for x in range(N):
            s = B(a, X[x], q); t = B(a2, X[x], q)
            cp[x] = pencil(s, t, q)
        # line classes: sums over its points
        cl = np.zeros(N, dtype=np.int64)
        for l in range(N):
            ss = sum(B(a, X[x], q) for x in LP[l]) % q
            tt = sum(B(a2, X[x], q) for x in LP[l]) % q
            cl[l] = pencil(ss, tt, q)
        shift = int(rng.integers(0, n))
        phi = lambda c: ((c * n) // (q + 1) + shift) % n
        import os
        which = os.environ.get('PENCIL', 'both')   # both | k | r
        kv = np.array([phi(c) for c in list(cp) + list(cl)])
        rp = np.array([phi(c) for c in cp])
        if which == 'k':
            rp = rng.integers(0, n, N)
        if which == 'r':
            kv = rng.integers(0, n, 2 * N)
    else:
        kv = rng.integers(0, n, 2 * N)
        rp = rng.integers(0, n, N)
    # matching sigma: points -> lines, no incidence (distance >= 3)
    if mode == 'pencil_d3':
        sigma = np.zeros(N, dtype=np.int64)
        used = np.zeros(N, dtype=bool)
        order = rng.permutation(N)
        for p in order:
            dp, dl = dist_from_point(p, LP, PL)
            cand = [l for l in range(N) if dl[l] == 3 and not used[l]]
            if not cand:
                raise SystemExit('no d3 candidate')
            l = cand[int(rng.integers(0, len(cand)))]
            sigma[p] = l; used[l] = True
    else:
        # random bijection avoiding incidence
        while True:
            perm = rng.permutation(N)
            ok = True
            for p in range(N):
                if perm[p] in set(PL[p]):
                    ok = False; break
            if ok:
                break
        sigma = perm
    with open(out, 'w') as f:
        f.write(f'D {n}\n{2 * N}\n')
        f.write(' '.join(['0'] * N + ['1'] * N) + '\n')
        for p in range(N):
            for l in PL[p]:
                f.write(f'{p} {N + l} 0\n')
        for v in range(2 * N):
            f.write(f'{v} {v} {n + int(kv[v]) % n}\n')
        for p in range(N):
            f.write(f'{p} {N + int(sigma[p])} {int(rp[p]) % n}\n')


if __name__ == '__main__':
    main()
