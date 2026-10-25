# shapes.py: other orbit shapes (k, m, f) for Haar graphs H(G,S), D = 7, |S| = 5 (round 2).
# S = {e} (if f >= 1) + (f-1) alpha-fixed elements + m alpha-orbits of size k, with f + k*m = 5 (haar_sym's ORBIT="k m f").
# alpha = conj(c) o (z -> r z), of order k exactly (k in {2,4,5}). Exhaustive when the count is <= LIMIT, else random sample.
# usage: python3 shapes.py NAME K M F [NAME K M F ...]   (NAME from r2sweep.CATALOG)
import sys, os, time, itertools, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'raise-d5D7-tools'))
import numpy as np
from math import comb
from fam import ecc_ok
import r2sweep as R

LIMIT = int(os.environ.get("LIMIT", "30000"))

def perm_order(a, idn):   # order of the permutation a
    y = a.copy(); o = 1
    while not np.array_equal(y, idn):
        y = a[y]; o += 1
        if o > 200: return 0
    return o

def alphas_of_order(M, inv, n_cyc, orders):
    N = M.shape[0]; idn = np.arange(N, dtype=np.int64)
    # classes of c with conj order in `orders` (c itself of order dividing lcm)
    seen = set(); reps = []
    for x in range(1, N):
        if x in seen: continue
        seen |= set(M[M[:, x], inv].tolist()); reps.append(x)
    rs = [1]
    if n_cyc > 2: rs += [r for r in range(2, n_cyc) if np.gcd(r, n_cyc) == 1]
    out = []
    for c in [None] + reps:
        for r in rs:
            a = idn.copy()
            if c is not None: a = M[M[c, :], inv[c]].astype(np.int64)
            if r != 1: a = (a // n_cyc) * n_cyc + ((a % n_cyc) * r) % n_cyc
            if np.array_equal(a, idn): continue
            o = perm_order(a, idn)
            if o in orders: out.append(((c, r), a, o))
    return out

def orbits_of(a, idn):
    N = len(a); seen = np.zeros(N, bool); res = {}
    for x in range(N):
        if seen[x]: continue
        o = [x]; y = int(a[x])
        while y != x: o.append(y); y = int(a[y])
        for y in o: seen[y] = True
        res.setdefault(len(o), []).append(o)
    return res

def run(name, spec, k, m, f, verbose=True):
    t0 = time.time()
    M = R.build_group(spec); N = M.shape[0]; inv = R.inverse_table(M); e = 0
    n_cyc = int(spec[-1][1:]) if spec[-1].startswith('Z') else 1
    idn = np.arange(N, dtype=np.int64)
    rng = random.Random(1)
    best = None; nfam = 0; hits = []
    for key, a, o in alphas_of_order(M, inv, n_cyc, {k}):
        nfam += 1
        orb = orbits_of(a, idn)
        fixed = [x[0] for x in orb.get(1, []) if x[0] != e]
        korb = orb.get(k, [])
        ntot = comb(len(fixed), f - 1) * comb(len(korb), m) if f >= 1 else comb(len(korb), m)
        hit = None; tried = 0
        if ntot <= LIMIT:
            combos_f = itertools.combinations(fixed, f - 1) if f >= 1 else [()]
            cand_iter = ((cf, co) for cf in combos_f for co in itertools.combinations(range(len(korb)), m))
        else:
            def gen():
                for _ in range(LIMIT):
                    cf = tuple(rng.sample(fixed, f - 1)) if f >= 1 else ()
                    co = tuple(rng.sample(range(len(korb)), m))
                    yield cf, co
            cand_iter = gen()
        for cf, co in cand_iter:
            S = ([e] if f >= 1 else []) + list(cf)
            for j in co: S += korb[j]
            if len(set(S)) != 5: continue
            tried += 1
            if ecc_ok(N, M, S, [int(inv[s]) for s in S], e):
                hit = S; break
        if verbose: print(f"{name} N={N} shape=({k},{m},{f}) alpha(c,r)={key[0]},{key[1]} ord={k} |Fix|={len(fixed)+1} "
                          f"korb={len(korb)} count={ntot} {'exh' if ntot <= LIMIT else 'rand'} tried={tried} HIT={hit}", flush=True)
        if hit: hits.append((key, hit)); break
    if verbose: print(f"{name} N={N} shape=({k},{m},{f}) families={nfam} hits={len(hits)} t={time.time()-t0:.0f}s", flush=True)
    return hits

if __name__ == '__main__':
    args = sys.argv[1:]
    for i in range(0, len(args), 4):
        nm, k, m, f = args[i], int(args[i+1]), int(args[i+2]), int(args[i+3])
        run(nm, R.CATALOG[nm], k, m, f)
