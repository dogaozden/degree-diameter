#!/usr/bin/env python3
"""Card c4 (squad round 2): unions of orbits of cyclic subgroups of O(7,11) on the points of H(11).

For a subgroup H of the isometry group of B (x^T J y), the H-orbits on the 177,156 points are computed. An orbit is
"good" iff its points are pairwise opposite (B != 0). Two good orbits are compatible iff all cross pairs are opposite,
which (H preserves B) is decided by one representative per orbit. A maximum-weight clique (weight = orbit size) is
searched by iterated local search. The union of the chosen orbits is a partial ovoid.

usage: python3 orbit_union.py   (env C4_CPU = internal CPU-time limit in seconds, C4_SEED = rng seed)
"""
import os, sys, time
import numpy as np

sys.path.insert(0, '/home/user/degree-diameter/research/d13D7/tools')
import hexlib

OUT = os.path.dirname(os.path.abspath(__file__))
CPU_LIMIT = float(os.environ.get('C4_CPU', '420'))
KMAX = int(os.environ.get('C4_KMAX', '6000'))
T0 = time.process_time()


def cpu():
    return time.process_time() - T0


def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    with open(os.path.join(OUT, 'run.log'), 'a') as f:
        f.write(s + '\n')


p = 11
_q, _lines, P = hexlib.load()
P = P.astype(np.int64)
N = len(P)
J = np.zeros((7, 7), np.int64)
J[0, 4] = J[4, 0] = J[1, 5] = J[5, 1] = J[2, 6] = J[6, 2] = 1
J[3, 3] = p - 2
I7 = np.eye(7, dtype=np.int64)
PW = p ** np.arange(7, dtype=np.int64)
CODES = P @ PW
assert np.all(np.diff(CODES) > 0)
INV = np.array([0, 1, 6, 4, 3, 9, 2, 8, 7, 5, 10], np.int64)
PJ = (P @ J) % p                                   # row i = J x_i (J symmetric)
NO = 2 * 11 ** 9 * (11 ** 2 - 1) * (11 ** 4 - 1) * (11 ** 6 - 1)   # |O(7,11)|
PRIMES = [2, 3, 5, 7, 11, 19, 37, 61]               # primes dividing |O(7,11)|


def mmul(a, b):
    return (a @ b) % p


def mpow(g, e):
    R = I7.copy()
    B = g.copy()
    while e:
        if e & 1:
            R = mmul(R, B)
        B = mmul(B, B)
        e >>= 1
    return R


def order_of(g):
    """exact order of an isometry g (its order divides |O(7,11)|)."""
    m = NO
    for pr in PRIMES:
        while m % pr == 0 and np.array_equal(mpow(g, m // pr), I7):
            m //= pr
    return m


def is_isom(g):
    return np.array_equal(mmul(mmul(g.T, J), g), J % p)


def refl(v):
    c = int(v @ J @ v) % p
    cinv = pow(c, p - 2, p)
    return (I7 - 2 * cinv * np.outer(v, (J @ v) % p)) % p


def rand_isom(rng, k):
    g = I7.copy()
    for _ in range(k):
        while True:
            v = rng.integers(0, p, 7)
            if int(v @ J @ v) % p:
                break
        g = mmul(refl(v), g)
    return g


def perm_of(g):
    """permutation of point indices induced by g (x -> g x, renormalised)."""
    Y = (P @ g.T) % p
    lead_idx = (Y != 0).argmax(axis=1)
    lead = Y[np.arange(N), lead_idx]
    Y = (Y * INV[lead][:, None]) % p
    codes = Y @ PW
    idx = np.searchsorted(CODES, codes)
    assert np.array_equal(CODES[idx], codes), 'image is not a point of Q'
    return idx


def components(perms):
    """connected components of the graph i -~ perm(i) (orbits of the generated group), min-label propagation."""
    lab = np.arange(N)
    while True:
        old = lab.copy()
        for pi in perms:
            vals = lab.copy()
            lab = np.minimum(lab, vals[pi])
            np.minimum.at(lab, pi, vals)
        lab = lab[lab]
        if np.array_equal(lab, old):
            break
    _, lab = np.unique(lab, return_inverse=True)
    return lab.astype(np.int64)


def analyse(gens):
    perms = [perm_of(g) for g in gens]
    lab = components(perms)
    ncomp = int(lab.max()) + 1
    sizes = np.bincount(lab, minlength=ncomp)
    _, rep = np.unique(lab, return_index=True)
    rep_of = rep[lab]
    b = (PJ[rep_of] * P).sum(axis=1) % p            # B(rep, x) for every point x
    bad_pt = (b == 0) & (np.arange(N) != rep_of)    # a non-representative point perpendicular to its rep
    bad = np.zeros(ncomp, bool)
    bad[lab[bad_pt]] = True
    good = np.flatnonzero(~bad)
    return lab, sizes, rep, good


def compat(lab, rep, good):
    """A[k, j] = True iff good orbits k and j are compatible (all cross pairs opposite)."""
    ncomp = rep.size
    K = good.size
    pos = np.full(ncomp, -1, np.int64)
    pos[good] = np.arange(K)
    pts = np.flatnonzero(pos[lab] >= 0)
    pl = pos[lab[pts]]
    o = np.argsort(pl, kind='stable')
    pts = pts[o]
    pl = pl[o]
    starts = np.searchsorted(pl, np.arange(K))
    PJs = PJ[pts]
    reps = P[rep[good]]
    A = np.zeros((K, K), bool)
    blk = 64
    for s in range(0, K, blk):
        Bm = (PJs @ reps[s:s + blk].T) % p          # B(point, rep_j)
        Z = (Bm == 0).astype(np.float32)
        C = np.add.reduceat(Z, starts, axis=0)      # perpendicular points per orbit
        A[:, s:s + blk] = (C == 0)
    np.fill_diagonal(A, False)
    return A


def mwc(A, w, rng, tlim, maxit=10 ** 7):
    """iterated local search for a maximum-weight clique of the graph A (weights w)."""
    K = w.size
    wf = w.astype(np.float64)

    def extend(S, cand):
        S = list(S)
        while True:
            idx = np.flatnonzero(cand)
            if idx.size == 0:
                return S
            v = int(idx[np.argmax(wf[idx] + 0.5 * rng.random(idx.size))])
            S.append(v)
            cand &= A[v]
            cand[v] = False

    def weight(S):
        return int(w[S].sum()) if len(S) else 0

    v0 = int(rng.integers(K))
    cur = extend([v0], A[v0].copy())
    curw = weight(cur)
    best, bestw = list(cur), curw
    it = 0
    while cpu() < tlim and it < maxit:
        it += 1
        inS = np.zeros(K, bool)
        inS[cur] = True
        conf = (~A[cur]).sum(axis=0)
        tol = 1 + (it % 3)
        ok = np.flatnonzero((~inS) & (conf <= tol))
        if ok.size == 0:
            ok = np.flatnonzero(~inS)
        v = int(ok[rng.integers(ok.size)])
        S2 = [u for u in cur if A[v, u]] + [v]
        inS2 = np.zeros(K, bool)
        inS2[S2] = True
        cand = np.all(A[S2], axis=0) & ~inS2
        S3 = extend(S2, cand)
        w3 = weight(S3)
        if w3 >= curw or rng.random() < 0.02:
            cur, curw = S3, w3
        if w3 > bestw:
            best, bestw = list(S3), w3
        if it % 300 == 0 and curw < bestw:
            cur, curw = list(best), bestw
    return best, bestw


def pairwise_ok(idx):
    idx = np.asarray(idx)
    if len(set(idx.tolist())) != len(idx):
        return False
    X = P[idx]
    G = (X @ J @ X.T) % p
    np.fill_diagonal(G, 1)
    return bool(np.all(G != 0))


def evaluate(gens, rng, tlim):
    lab, sizes, rep, good = analyse(gens)
    K = good.size
    if K == 0:
        return 0, None, 0
    if K > KMAX:
        return -1, None, K
    A = compat(lab, rep, good)
    w = sizes[good]
    best, bestw = mwc(A, w, rng, tlim)
    chosen = good[best]
    idx = np.flatnonzero(np.isin(lab, chosen))
    assert idx.size == bestw
    return bestw, idx, K


def main():
    rng = np.random.default_rng(int(os.environ.get('C4_SEED', '1')))
    # sanity checks
    assert is_isom(rand_isom(rng, 6)) and is_isom(rand_isom(rng, 5))
    best_w, best_idx, best_desc = 0, None, ''
    log('start, N =', N, 'cpu limit', CPU_LIMIT)
    evals = 0
    while cpu() < CPU_LIMIT - 20:
        k = int(rng.integers(4, 13))
        g = rand_isom(rng, k)
        assert is_isom(g)
        m = order_of(g)
        divs = [d for d in range(5, 1400) if m % d == 0]
        for d in divs:
            if cpu() > CPU_LIMIT - 20:
                break
            h = mpow(g, m // d)
            tl = min(CPU_LIMIT - 10, cpu() + float(os.environ.get('C4_TL', '6')))
            t1 = cpu()
            bw, idx, K = evaluate([h], rng, tl)
            evals += 1
            log(f'order {d} (k={k}, |g|={m}): good orbits K={K}, best weight {bw}, '
                f'eval cpu {cpu() - t1:.1f}s')
            if idx is not None and bw > best_w:
                ok = pairwise_ok(idx)
                if ok:
                    best_w, best_idx = bw, idx
                    best_desc = f'cyclic order {d}'
                    np.savetxt(os.path.join(OUT, 'best_idx.txt'), np.sort(best_idx), fmt='%d')
                    log(f'NEW BEST {best_w} from {best_desc}')
                else:
                    log('pairwise check FAILED for a candidate; ignored')
    log('done: evals', evals, 'best', best_w, best_desc, 'cpu', round(cpu(), 1))


if __name__ == '__main__':
    main()
