import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS_G = 1200                # annealing moves per lift attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # base vertices per side
GQ_Q_MAX = 9                  # largest q for which W(q) is built
RETRIES = 2                   # annealing attempts per lift order
TIME_FRAC = 0.8               # fraction of time_limit used overall
EXTEND_SLICE = 0.5            # seconds per greedy extension run
EXTEND_TRIES = 6              # randomized greedy restarts per base graph
POOL_KEEP = 8                 # candidates kept in the pool
BC_N_MAX = 1600               # largest group order searched for bi-Cayley graphs
BC_GROUPS_PER_ORDER = 6       # group presentations tried per order in one attempt
BC_SLICE0 = 0.2               # initial seconds per order attempt
BOLD_FRAC = 0.6               # share of working time for the bold bi-Cayley search
HAAR_FRAC = 0.1               # share of remaining time for Haar search
POST_FRAC = 0.1               # share of total working time reserved for final extension


# ---------------------------------------------------------------- algebraic bases

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """W(q) for the largest prime power q <= min(d-1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- extension helpers

def _two_colour(n, edges):
    """Proper 2-colouring of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add vertices, each attached to a set cover of the current graph."""
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            covered, chosen = 0, []
            while covered != full and len(chosen) < d and cand:
                best_u, best_gain = -1, 0
                for u in cand:
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_u, best_gain = u, g
                if best_u < 0:
                    break
                chosen.append(best_u)
                covered |= balls[best_u]
                cand.remove(best_u)
            if covered == full and chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _extend_best(n, edges, d, D, rng, deadline, tries=EXTEND_TRIES):
    """Several randomized greedy extensions, keeping the largest result."""
    best = (n, list(edges))
    for t in range(tries):
        now = time.monotonic()
        if now >= deadline:
            break
        per = now + (deadline - now) / (tries - t)
        cand = _extend(n, edges, d, D, rng, per)
        if cand[0] > best[0]:
            best = cand
    return best


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree."""
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _grow_alt(n, edges, d, D, rng, deadline):
    """Alternate spare-degree edge augmentation and greedy cover extension."""
    for _ in range(4):
        if time.monotonic() >= deadline:
            break
        _, e2 = _augment(n, edges, d, rng.randrange(1 << 30))
        n2, e3 = _extend(n, e2, d, D, rng, deadline)
        if n2 == n and len(e2) == len(edges):
            break
        n, edges = n2, e3
    return n, edges


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- Haar graphs

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ---------------------------------------------------------------- semidirect groups
#
# Group Z_m x|_r Z_k, element (a, b) coded as a*k + b, product (a,b)(c,d) = (a + r^b c, b + d).

def _presentations(M, rng, limit):
    """Random semidirect presentations (m, k, r) of groups of order M (k <= 8)."""
    out = []
    ks = [k for k in range(1, 9) if M % k == 0]
    rng.shuffle(ks)
    for k in ks:
        m = M // k
        if m == 1:
            out.append((1, k, 0))
        elif k == 1:
            out.append((m, 1, 1))
        else:
            cands = [m - 1] if k == 2 else []
            for _ in range(40):
                r = rng.randrange(1, m)
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    cands.append(r)
            if cands:
                out.append((m, k, rng.choice(cands)))
        if len(out) >= limit:
            break
    return out


def _group_tables(m, k, r):
    """Return (N, tab, invs): tab[s, x] = x * s, invs[s] = s^{-1}, for G = Z_m x|_r Z_k."""
    N = m * k
    pw = [pow(r, b, m) for b in range(k)]
    pw_arr = np.array(pw, dtype=np.int64)
    X = np.arange(N, dtype=np.int64)
    A, B = X // k, X % k
    tab = np.empty((N, N), dtype=np.int32)
    invs = np.empty(N, dtype=np.int64)
    for s in range(N):
        c, dd = divmod(s, k)
        tab[s] = ((A + pw_arr[B] * c) % m) * k + (B + dd) % k
        nb = (-dd) % k
        na = (-pw[nb] * c) % m
        invs[s] = na * k + nb
    return N, tab, invs


class _Grp:
    """Semidirect group Z_m x|_r Z_k of order M = m*k with vectorised right multiplication."""

    def __init__(self, m, k, r):
        self.m, self.k, self.r = m, k, r
        self.M = m * k
        self.powers = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        X = np.arange(self.M, dtype=np.int64)
        a, b = X // k, X % k
        nb = (-b) % k
        c = (-self.powers[nb] * a) % m
        self.inv = c * k + nb

    def mul(self, X, g):
        """Return X * g elementwise (X an array, g a scalar element)."""
        a1, b1 = X // self.k, X % self.k
        a2, b2 = g // self.k, g % self.k
        a = (a1 + self.powers[b1] * a2) % self.m
        b = (b1 + b2) % self.k
        return a * self.k + b


# ---------------------------------------------------------------- group lifts (annealing)

def _gcol(nbr, kk, sig, sinv, G, s, M, grp):
    """Fill neighbour column kk for every lift vertex."""
    Y = np.arange(M, dtype=np.int64)
    for i in range(s):
        j = int(sig[kk, i])
        nbr[i * M:(i + 1) * M, kk] = s * M + j * M + grp.mul(Y, int(G[kk, i]))
    for j in range(s):
        i = int(sinv[kk, j])
        gi = int(grp.inv[int(G[kk, i])])
        nbr[s * M + j * M: s * M + (j + 1) * M, kk] = i * M + grp.mul(Y, gi)


def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D."""
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        Mx = R.copy()
        for k in range(nbr.shape[1]):
            Mx |= R[:, nbr[:, k]]
        if np.array_equal(Mx, R):
            break
        R = Mx
    return int(S * n - np.count_nonzero(R))


def _lift_anneal(s, M, grp, d, D, rng, deadline, iters):
    """Anneal darts of a group lift until diameter <= D. Returns neighbour table or None."""
    n = 2 * s * M
    sig = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    sinv = np.zeros_like(sig)
    for kk in range(d):
        for i in range(s):
            sinv[kk, sig[kk, i]] = i
    G = np.array([[rng.randrange(M) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    nbr = np.empty((n, d), dtype=np.int64)
    for kk in range(d):
        _gcol(nbr, kk, sig, sinv, G, s, M, grp)
    sources = [i * M for i in range(s)] + [s * M + j * M for j in range(s)]
    cur = _cost(nbr, sources, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / iters) + 0.05
        if s == 1 or rng.random() < 0.6:
            kk, i = rng.randrange(d), rng.randrange(s)
            old = int(G[kk, i])
            new = rng.randrange(M)
            if new == old:
                continue
            G[kk, i] = new
            _gcol(nbr, kk, sig, sinv, G, s, M, grp)
            c = _cost(nbr, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                G[kk, i] = old
                _gcol(nbr, kk, sig, sinv, G, s, M, grp)
        else:
            kk = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(sig, sinv, kk, a, b)
            _gcol(nbr, kk, sig, sinv, G, s, M, grp)
            c = _cost(nbr, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                _swap(sig, sinv, kk, a, b)
                _gcol(nbr, kk, sig, sinv, G, s, M, grp)
    return nbr if cur == 0 else None


def _nbr_edges(nbr):
    """Deduplicated edge list from a neighbour table."""
    n, d = nbr.shape
    xs = np.repeat(np.arange(n, dtype=np.int64), d)
    ys = nbr.reshape(-1)
    lo = np.minimum(xs, ys)
    hi = np.maximum(xs, ys)
    keys = np.unique(lo * n + hi)
    return [(int(x // n), int(x % n)) for x in keys.tolist()]


def _lift_try(s, M, d, D, rng, deadline):
    """Try a few random presentations of order M. Returns edge list or None."""
    pres = _presentations(M, rng, 4)
    for _ in range(RETRIES):
        if time.monotonic() >= deadline:
            break
        m, k, r = rng.choice(pres)
        grp = _Grp(m, k, r)
        nbr = _lift_anneal(s, M, grp, d, D, rng, deadline, ITERS_G)
        if nbr is not None:
            return _nbr_edges(nbr)
    return None


def _lift_search(s, d, D, rng, deadline, cap):
    """Doubling then bisection over group order M for a fixed base size s."""
    best = None
    lo, hi = 0, None
    M = max(2, d)
    while time.monotonic() < deadline:
        if 2 * s * M > cap:
            if lo == 0:
                break
            hi = M
        else:
            edges = _lift_try(s, M, d, D, rng, deadline)
            if edges is not None:
                lo = M
                best = (2 * s * M, edges)
            elif lo == 0:
                M *= 2
                continue
            else:
                hi = M
        if hi is None:
            M = 2 * M
        else:
            if hi - lo <= max(1, lo // 16):
                break
            M = (lo + hi) // 2
    return best


# ---------------------------------------------------------------- bold bi-Cayley search
#
# Left vertex x is joined to right vertex x*s for s in S, over a group G of order N.
# Groups: (Z_m x|_r Z_k) x Z_t, so every factorisation N = m*k*t is searched, not only
# semidirect ones. Orders are scanned upward, keeping the largest order that succeeds.

def _bc_groups(N, rng, limit):
    """Random presentations (m, k, r, t) of groups of order N, as (Z_m x|_r Z_k) x Z_t."""
    cands = set()
    for k in range(1, 9):
        if N % k:
            continue
        rest = N // k
        for t in range(1, rest + 1):
            if rest % t:
                continue
            m = rest // t
            rs = {1 % m}
            if k == 2 and m > 2:
                rs.add(m - 1)
            if k > 1 and m > 2:
                for _ in range(12):
                    r = rng.randrange(2, m)
                    if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                        rs.add(r)
            for r in rs:
                cands.add((m, k, r, t))
    lst = sorted(cands)
    rng.shuffle(lst)
    return lst[:limit]


def _bc_tab(m, k, r, t):
    """Right-multiplication table tab[s, x] = x*s and inverses for (Z_m x|_r Z_k) x Z_t.

    Raises ValueError if the table is not a group (then the caller skips it).
    """
    _, tabH, _ = _group_tables(m, k, r)
    tabH = tabH.astype(np.int64)
    N = m * k * t
    X = np.arange(N, dtype=np.int64)
    xh, xe = X // t, X % t
    tab = np.empty((N, N), dtype=np.int64)
    for s in range(N):
        sh, se = divmod(s, t)
        tab[s] = tabH[sh][xh] * t + (xe + se) % t
    invs = np.empty(N, dtype=np.int64)
    for s in range(N):
        z = np.flatnonzero(tab[s] == 0)
        if z.size == 0:
            raise ValueError("not a group")
        invs[s] = z[0]
    return tab, invs


def _bc_uncovered(tab, invs, S, N, D):
    """Number of (source, vertex) pairs NOT within distance D, sources (L, e) and (R, e)."""
    fwd = [tab[s] for s in S]
    bwd = [tab[invs[s]] for s in S]
    total = 0
    for side in (0, 1):
        visL = np.zeros(N, dtype=bool)
        visR = np.zeros(N, dtype=bool)
        if side == 0:
            visL[0] = True
            fL = np.array([0], dtype=np.int64)
            fR = np.empty(0, dtype=np.int64)
        else:
            visR[0] = True
            fR = np.array([0], dtype=np.int64)
            fL = np.empty(0, dtype=np.int64)
        for _ in range(D):
            nR = np.zeros(N, dtype=bool)
            if fL.size:
                for row in fwd:
                    nR[row[fL]] = True
            nL = np.zeros(N, dtype=bool)
            if fR.size:
                for row in bwd:
                    nL[row[fR]] = True
            nR &= ~visR
            nL &= ~visL
            visR |= nR
            visL |= nL
            fL = np.flatnonzero(nL)
            fR = np.flatnonzero(nR)
            if fL.size == 0 and fR.size == 0:
                break
        total += 2 * N - int(visL.sum()) - int(visR.sum())
    return total


def _bc_anneal(N, tab, invs, d, D, rng, end):
    """Search a connection set S of size d with zero uncovered pairs. Returns S or None."""
    if d > N:
        return None
    S = rng.sample(range(N), d)
    cur = _bc_uncovered(tab, invs, S, N, D)
    t0 = time.monotonic()
    span = max(1e-3, end - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= end:
            break
        temp = 1.2 * (1.0 - (now - t0) / span) + 0.05
        i = rng.randrange(d)
        t = rng.randrange(N)
        if t in S:
            continue
        T = S[:]
        T[i] = t
        c = _bc_uncovered(tab, invs, T, N, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            S, cur = T, c
    return S if cur == 0 else None


def _bc_graph(N, tab, S):
    """Bi-Cayley graph: left x joined to right N + x*s for s in S."""
    edges = []
    for s in S:
        row = tab[s].tolist()
        for x in range(N):
            edges.append((x, N + row[x]))
    return 2 * N, edges


def _bc_try_order(N, d, D, rng, end):
    """Try to realise a valid bi-Cayley graph of order N over several group presentations."""
    cands = _bc_groups(N, rng, BC_GROUPS_PER_ORDER)
    for idx, (m, k, r, t) in enumerate(cands):
        now = time.monotonic()
        if now >= end:
            break
        per_end = now + (end - now) / (len(cands) - idx)
        try:
            tab, invs = _bc_tab(m, k, r, t)
        except Exception:
            continue
        S = _bc_anneal(N, tab, invs, d, D, rng, per_end)
        if S is not None:
            return _bc_graph(N, tab, S)
    return None


def _bold_bc(d, D, seed, deadline):
    """Ascending scan over group orders, keeping the largest order with a valid bi-Cayley graph."""
    moore = lib._moore_bound(d, D)
    N_hi = min(N_CAP // 2, moore // 2, BC_N_MAX)
    N_lo = max(d, N_hi // 3)
    if N_hi < N_lo or N_hi < d:
        return None
    rng = random.Random(seed * 1000003 + 17 * d + D + 5)
    best = None
    best_N = N_lo - 1
    slice_t = BC_SLICE0
    while time.monotonic() < deadline - 0.2:
        improved = False
        for N in range(best_N + 1, N_hi + 1):
            now = time.monotonic()
            if now >= deadline - 0.2:
                break
            g = _bc_try_order(N, d, D, rng, min(deadline, now + slice_t))
            if g is not None:
                best_N, best = N, g
                improved = True
                break
        if not improved:
            if best_N + 1 > N_hi:
                break
            slice_t *= 2
    return best


# ---------------------------------------------------------------- legacy pipeline

def _legacy_pool(d, D, seed, start, deadline):
    """Algebraic bases, extensions, Haar graphs and group lifts. Returns a list of candidates."""
    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))
    pool = [lib.haar_graph(d, range(d))]

    def add(c):
        if c is None:
            return
        pool.append(c)
        pool.sort(key=lambda item: -item[0])
        del pool[POOL_KEEP:]

    pg = _pg_base(d) if D == 3 else None
    gq = _best_gq(d) if D >= 4 else None
    if D == 3 and pg is not None and lib.is_prime_power(d - 1):
        return [pg]
    if D == 4 and gq is not None and lib.is_prime_power(d - 1) and d - 1 <= GQ_Q_MAX:
        return [gq]

    base = pg if D == 3 else gq
    if base is not None:
        add(base)
        alg_end = min(deadline, time.monotonic() + 0.15 * max(0.0, deadline - start))
        aug = _augment(base[0], base[1], d, seed)
        add(aug)
        for h in (base, aug):
            now = time.monotonic()
            if now >= alg_end:
                break
            add(_extend_best(h[0], h[1], d, D, rng, min(alg_end, now + EXTEND_SLICE)))
        now = time.monotonic()
        if now < alg_end:
            add(_grow_alt(aug[0], aug[1], d, D, rng, min(alg_end, now + EXTEND_SLICE)))

    # Haar graphs with growing modulus.
    now = time.monotonic()
    haar_end = now + HAAR_FRAC * max(0.0, deadline - now)
    haar_m, haar_miss, haar_best = d + 1, 0, None
    while time.monotonic() < haar_end and haar_miss < 4 and 2 * haar_m <= cap:
        S = _search_haar(d, D, haar_m, rng, haar_end, 120)
        if S is not None:
            haar_best = lib.haar_graph(haar_m, S)
            haar_miss = 0
        else:
            haar_miss += 1
        haar_m += 1
    add(haar_best)

    # Cyclic, dihedral and semidirect group lifts, one slice per base size.
    post_reserve = POST_FRAC * max(0.0, deadline - start)
    lift_end = deadline - post_reserve
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= lift_end:
            break
        slice_end = now + (lift_end - now) / (len(S_LIST) - idx)
        try:
            add(_lift_search(s, d, D, rng, slice_end, cap))
        except Exception:
            pass

    # Post-processing: fill spare degree of the best candidate.
    if pool:
        top = pool[0]
        try:
            add(_extend_best(top[0], top[1], d, D, rng, deadline, tries=2))
        except Exception:
            pass

    return pool


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    work = max(0.5, TIME_FRAC * time_limit - 1.0)
    deadline = start + work
    pool = []

    # Bold search: bi-Cayley graphs over a broad family of groups (weak regime d >= 4, D >= 4).
    if d >= 4 and D >= 4:
        try:
            g = _bold_bc(d, D, seed, start + BOLD_FRAC * work)
            if g is not None:
                pool.append(g)
        except Exception:
            pass

    # Legacy pipeline gets the rest of the time and always contributes the safe Haar fallback.
    try:
        pool.extend(_legacy_pool(d, D, seed, start, deadline))
    except Exception:
        pass

    try:
        return _finish(pool, d, D)
    except Exception:
        return lib.haar_graph(d, range(d))
