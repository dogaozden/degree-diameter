# r2frob.py: order-3 automorphisms of AGL(1,8) x Z_n that are outer (Frobenius x -> x^2 on GF(8), composed with inner
# conjugations and z -> r z), then the same exhaustive k=3 orbit families as r2sweep.run.
# AGL(1,8) has order 56 = 2^3 * 7: no inner automorphism of order 3, so r2sweep never produced these families.
# usage: python3 -I r2frob.py AGL18 n [n ...]   (group AGL(1,8) x Z_n, n in the target order range)
import sys, os, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import r2sweep as R
from fam import ecc_ok, family

def frob_perm_on_points():
    # GF(8) = GF(2)[x]/(x^3+x+1); points are ints 0..7 (bit i = coefficient of x^i); sigma(x) = x^2
    q, mul = R.gf(2, 3, [1, 1, 0])
    return tuple(mul(x, x) for x in range(q))

def automorphisms_H(gens_pts, sigma):
    """All order-3 automorphisms of H = <gens_pts> (perm group on points) of the form sigma-conj o inner conj."""
    H_els = R.closure(gens_pts)
    ix = {p: k for k, p in enumerate(H_els)}
    n = len(H_els[0]); sinv = [0] * n
    for i, s in enumerate(sigma): sinv[s] = i
    def conj(p, g):   # g p g^-1 for perm tuples (apply right-to-left as composition g o p o g^-1)
        ginv = [0] * n
        for i, s in enumerate(g): ginv[s] = i
        return tuple(g[p[ginv[x]]] for x in range(n))
    out = {}
    for s_pow in (0, 1):
        sig = tuple(range(n)) if s_pow == 0 else sigma
        sig_inv = [0] * n
        for i, s in enumerate(sig): sig_inv[s] = i
        base = np.array([ix[tuple(sig[p[sig_inv[x]]] for x in range(n))] for p in H_els], dtype=np.int64)
        for h in range(len(H_els)):
            a = np.array([ix[conj(H_els[base[i]], H_els[h])] for i in range(len(H_els))], dtype=np.int64)
            key = a.tobytes()
            if key not in out: out[key] = (s_pow, h, a)
    return list(out.values()), H_els, ix

def run(n):
    t0 = time.time()
    # AGL(1,8) generators as perms of the 8 points: translation by 1 (XOR) and multiplication by x (= 2)
    _, mul = R.gf(2, 3, [1, 1, 0])
    gens = [tuple(x ^ 1 for x in range(8)), tuple(mul(2, x) for x in range(8))]
    sigma = frob_perm_on_points()
    H_auts, H_els, ix = automorphisms_H(gens, sigma)
    H = np.array(H_els, dtype=np.int64)
    Hh = len(H_els)
    spec = ['AGL18', f'Z{n}']
    M = R.build_group(spec); N = M.shape[0]; inv = R.inverse_table(M); e = 0
    idn = np.arange(N, dtype=np.int64)
    rs = [1] + [r for r in range(2, n) if np.gcd(r, n) == 1 and pow(r, 3, n) == 1]
    fams = []
    for s_pow, h, aH in H_auts:
        for r in rs:
            a = np.empty(N, dtype=np.int64)
            for hz in range(N):
                hh, z = divmod(hz, n)
                a[hz] = int(aH[hh]) * n + (r * z) % n
            if np.array_equal(a, idn): continue
            if not (a[a[a]] == idn).all(): continue
            fams.append(((s_pow, h, r), a))
    print(f"AGL18xZ{n} N={N} |H|={Hh} outer-or-inner order-3 alphas={len(fams)} (outer: {sum(1 for k,_ in fams if k[0]==1)})", flush=True)
    for key, a in fams:
        fix, orbits = family(N, M, a, e)
        hit = None; ntried = 0
        for t in fix:
            if t == e: continue
            for o in orbits:
                S = [e, int(t)] + o
                if len(set(S)) != 5: continue
                ntried += 1
                if ecc_ok(N, M, S, [int(inv[s]) for s in S], e): hit = S; break
            if hit: break
        print(f"AGL18xZ{n} N={N} alpha(sigma={key[0]},h={key[1]},r={key[2]}) |Fix|={len(fix)} orbits={len(orbits)} tried={ntried} HIT={hit}", flush=True)
        if hit: return key, hit
    print(f"AGL18xZ{n} done t={time.time()-t0:.0f}s none", flush=True)
    return None

if __name__ == '__main__':
    for n in sys.argv[1:]: run(int(n))
