import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact families for D = 3 and D = 4 (unchanged from the parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW construction: symmetric double covers of Cayley graphs.
#
# Let G be a finite group and S a symmetric set of d non-identity elements
# (S = S^-1). The bipartite double cover has vertices A_g and B_g (g in G),
# with A_g ~ B_{g s} for every s in S. Each vertex has degree d, the graph is
# bipartite by construction, and it has 2|G| vertices.
#
# By left-multiplication symmetry, the diameter is at most D iff the walks
# from the identity cover G within D steps: even-length walks reach every A
# vertex, and odd-length walks reach every B vertex. This is checked on the
# group directly with numpy, which makes each candidate evaluation cheap.
#
# Groups: Z_m x| Z_k with (a,b)(c,e) = (a + r^b c, b + e), so r = 1 gives
# the direct product and m = N gives the cyclic group.
#
# Search: for each target order N (increasing), sample a group, sample
# S (an odd or even number of involutions plus inverse pairs), and anneal
# on the uncovered count. Any success is verified with lib.is_valid.
# ----------------------------------------------------------------------------


def _cayley_try(N, d, D, rng, deadline, iters):
    """Try to find a symmetric generating set of size d in a group of order N.

    Returns (n, edges) for the double cover (n = 2N), or None.
    """
    ks = [k for k in range(1, N + 1) if N % k == 0]
    k = rng.choice(ks)
    m = N // k
    if m == 1:
        r = 0
    else:
        rs = [x for x in range(1, m) if math.gcd(x, m) == 1 and pow(x, k, m) == 1 % m]
        if not rs:
            return None
        r = rng.choice(rs)
    powtab = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)

    idx = np.arange(N, dtype=np.int64)
    A = idx // k
    B = idx % k
    pw = powtab[B]
    # MR[s, g] = index of g * s.
    MR = ((A[None, :] + pw[None, :] * A[:, None]) % m) * k + (B[None, :] + B[:, None]) % k
    # INV[s] = index of s^-1.
    ep = (-B) % k
    cp = (-(powtab[ep]) * A) % m
    INV = cp * k + ep
    invl = INV.tolist()

    involutions = [s for s in range(1, N) if invl[s] == s]
    reps = [s for s in range(1, N) if invl[s] != s and s < invl[s]]
    opts = [t for t in range(d % 2, min(d, len(involutions)) + 1, 2)
            if (d - t) // 2 <= len(reps)]
    if not opts:
        return None
    t = rng.choice(opts)
    p = (d - t) // 2
    inv_sel = rng.sample(involutions, t)
    pair_sel = rng.sample(reps, p)

    def gen_set():
        return inv_sel + pair_sel + [invl[s] for s in pair_sel]

    def cost(S):
        # E: elements reached by even-length walks from e (A side).
        # O: elements reached by odd-length walks from e (B side).
        E = np.zeros(N, dtype=bool)
        O = np.zeros(N, dtype=bool)
        E[0] = True
        cur = np.zeros(1, dtype=np.int64)
        for step in range(1, D + 1):
            nxt = np.zeros(N, dtype=bool)
            for s in S:
                nxt[MR[s][cur]] = True
            cur = np.flatnonzero(nxt)
            if cur.size == 0:
                break
            if step % 2:
                O[cur] = True
            else:
                E[cur] = True
        return 2 * N - int(E.sum()) - int(O.sum())

    cur_c = cost(gen_set())
    for it in range(iters):
        if cur_c == 0 or time.monotonic() > deadline:
            break
        T = 1.5 * (1.0 - it / iters) + 0.05
        if t > 0 and (p == 0 or rng.random() < 0.25):
            i = rng.randrange(t)
            new = rng.choice(involutions)
            if new in inv_sel:
                continue
            old = inv_sel[i]
            inv_sel[i] = new
            c = cost(gen_set())
            if c <= cur_c or rng.random() < math.exp(-(c - cur_c) / T):
                cur_c = c
            else:
                inv_sel[i] = old
        else:
            if p == 0:
                break
            i = rng.randrange(p)
            new = rng.choice(reps)
            if new in pair_sel:
                continue
            old = pair_sel[i]
            pair_sel[i] = new
            c = cost(gen_set())
            if c <= cur_c or rng.random() < math.exp(-(c - cur_c) / T):
                cur_c = c
            else:
                pair_sel[i] = old

    if cur_c != 0:
        return None
    S = gen_set()
    edges = []
    for s in S:
        row = MR[s].tolist()
        edges.extend((g, N + row[g]) for g in range(N))
    return 2 * N, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best
    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best
    if D == 2:
        return best

    # Ladder search over N: the double cover of a Cayley graph on N elements
    # has 2N vertices. Start from the current best and climb upward.
    rng = random.Random(seed)
    N = max(2, best_n // 2 + 1)
    try:
        while time.monotonic() < deadline:
            if d % 2 == 1 and N % 2 == 1:
                N += 1  # odd d needs an involution, so keep N even
            slice_end = min(deadline, time.monotonic() + 1.2)
            res = None
            tries = 0
            while res is None and time.monotonic() < slice_end and tries < 40:
                tries += 1
                res = _cayley_try(N, d, D, rng, slice_end, 2500)
            if res is not None and res[0] > best_n:
                consider(res[0], res[1])
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
