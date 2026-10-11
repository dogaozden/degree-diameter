import itertools
import math
import random
import time
from collections import Counter

import lib

MAX_GROUPS = 30        # groups tried per (a, N) attempt
ITERS = 900            # annealing steps per (group, base pattern) try
K_WINDOW = 6           # number of candidate totals tried per round
NCAP = 450             # largest group order N considered
KNOWN_RECORD = {(5, 5): 336}   # total-vertex records used as search anchors

_gcache = {}           # (m, k, r) -> (T, invs)
_grcache = {}          # N -> list of (m, k, r)


# ----------------------------------------------------------------------------
# Safe baseline families.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Lifts of a small bipartite base multigraph (a A-vertices, a B-vertices, each of
# degree d) over a group G of order N, using the semidirect products Z_m x| Z_k.
#
# Vertices: A_i,x -> i*N + x ; B_j,y -> a*N + j*N + y.
# Dart (i, j, g) gives edges A_i,x -- B_j,(x*g) for all x in G.
# Left multiplication is an automorphism, so eccentricities from A_i,e and
# B_j,e (one source per base vertex) decide the diameter.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    if N in _grcache:
        return _grcache[N]
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _grcache[N] = out
    return out


def _tables(m, k, r):
    """Multiplication table T[x][g] and inverse table for the group, cached."""
    key = (m, k, r)
    if key in _gcache:
        return _gcache[key]
    N = m * k
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    if len(_gcache) > 48:
        _gcache.clear()
    _gcache[key] = (T, invs)
    return T, invs


def _base_pattern(a, d, N, rng):
    """Random base multigraph with a A- and a B-vertices, all of degree d, connected.
    Returns a Counter of (i, j) multiplicities, or None."""
    for _ in range(40):
        pairs = []
        for _t in range(d):
            perm = list(range(a))
            rng.shuffle(perm)
            pairs.extend((i, perm[i]) for i in range(a))
        if a > 1:
            parent = list(range(2 * a))

            def find(x):
                while parent[x] != x:
                    parent[x] = parent[parent[x]]
                    x = parent[x]
                return x

            for i, j in pairs:
                parent[find(i)] = find(a + j)
            if len({find(x) for x in range(2 * a)}) > 1:
                continue
        counts = Counter(pairs)
        if max(counts.values()) > N:
            continue
        return counts
    return None


def _cost(N, a, T, invs, darts, D):
    """Total number of (source, vertex) pairs at distance > D over the 2a base sources."""
    AN = a * N
    V = 2 * AN
    dA = [[] for _ in range(a)]
    dB = [[] for _ in range(a)]
    for i, j, g in darts:
        dA[i].append((j, g))
        dB[j].append((i, invs[g]))
    srcs = [i * N for i in range(a)] + [AN + j * N for j in range(a)]
    total = 0
    for src in srcs:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < AN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in dA[i]:
                        v = AN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - AN, N)
                    row = T[y]
                    for i, h in dB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(N, a, T, invs, darts, D, rng, deadline):
    """Simulated annealing over the group labels of the darts."""
    cur = _cost(N, a, T, invs, darts, D)
    for it in range(ITERS):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = max(0.5, 3.0 * (1.0 - it / ITERS))
        e = rng.randrange(len(darts))
        i, j, g = darts[e]
        c = rng.randrange(N)
        if c == g:
            continue
        clash = False
        for f, (i2, j2, g2) in enumerate(darts):
            if f != e and i2 == i and j2 == j and g2 == c:
                clash = True
                break
        if clash:
            continue
        darts[e][2] = c
        v = _cost(N, a, T, invs, darts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[e][2] = g
    return darts if cur == 0 else None


def _attempt(N, a, d, D, rng, deadline):
    """Try groups of order N with a-part base lifts until one has diameter <= D."""
    if N <= d or N > NCAP:
        return None
    groups = list(_groups(N))
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() >= deadline:
            return None
        T, invs = _tables(m, k, r)
        counts = _base_pattern(a, d, N, rng)
        if counts is None:
            continue
        darts = []
        for (i, j), c in counts.items():
            for g in rng.sample(range(N), c):
                darts.append([i, j, g])
        res = _anneal(N, a, T, invs, darts, D, rng, deadline)
        if res is not None:
            return T, res
    return None


def _edges(N, a, T, darts):
    """Expand a lift into (n, edges)."""
    AN = a * N
    out = []
    for i, j, g in darts:
        for x in range(N):
            out.append((i * N + x, AN + j * N + T[x][g]))
    return 2 * AN, out


def _window(lo, Mtot, d, K):
    """The next K achievable (total, a, N) triples with total > lo."""
    out = []
    T = lo + 1
    while len(out) < K and T <= Mtot and T <= lo + 400:
        for a in (1, 2, 3):
            if T % (2 * a) == 0:
                N = T // (2 * a)
                if d < N <= NCAP:
                    out.append((T, a, N))
        T += 1
    return out[:K]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Calibration case with a known exact construction.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    Mtot = lib._moore_bound(d, D)
    rec = KNOWN_RECORD.get((d, D))

    # Phase 0: anchor at the known record total, so a fallback at least matches it.
    if rec and rec <= Mtot:
        phase0_end = start + 0.3 * time_limit
        for a in (1, 2, 3):
            if rec % (2 * a):
                continue
            N = rec // (2 * a)
            if N <= d or N > NCAP:
                continue
            now = time.monotonic()
            if now >= phase0_end:
                break
            res = _attempt(N, a, d, D, rng, min(phase0_end, now + 0.12 * time_limit))
            if res is not None:
                consider(*_edges(N, a, res[0], res[1]))
                break

    # Phase 1: search totals above the current best (or above the record anchor).
    lo_base = rec - 40 if rec else Mtot // 4
    budget = 0.5
    while time.monotonic() < deadline:
        lo_now = max(lo_base, best_n)
        win = _window(lo_now, Mtot, d, K_WINDOW)
        if not win:
            break
        success = False
        for T, a, N in win:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(N, a, d, D, rng, min(deadline, now + budget))
            if res is not None:
                consider(*_edges(N, a, res[0], res[1]))
                success = True
                break
        if not success:
            budget *= 1.6

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
