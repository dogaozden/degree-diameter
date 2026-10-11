import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one attempt
ITERS = 900                   # annealing steps per (group, voltage assignment) try
WINDOW = 6                    # candidate orders N tried per round
SAFETY = 0.80                 # fraction of time_limit we allow ourselves


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: 2+2 base multigraph lifted over semidirect groups Z_m x| Z_k.
#
# Base vertices A_0, A_1 (side A) and B_0, B_1 (side B). Each base vertex has
# total multiplicity d. A dart (i, j, g) joins A_{i,x} to B_{j, x*g} for all x.
# Left multiplication by the group is an automorphism, so the diameter is
# determined by BFS from one representative per base vertex (4 sources).
# Order of the lift is 4N. Voltages are searched by simulated annealing.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _cost(N, T, IV, darts, D):
    """Total number of (source, vertex) pairs at distance > D, over the 4 representative sources."""
    N2 = 2 * N
    outs = [[], []]
    ins = [[], []]
    for i, j, g in darts:
        outs[i].append((j, g))
        ins[j].append((i, IV[g]))
    total = 0
    for src in (0, N, N2, N2 + N):
        seen = bytearray(2 * N2)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N2:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outs[i]:
                        v = N2 + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - N2, N)
                    row = T[y]
                    for i, h in ins[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N2 - count
    return total


def _anneal(N, T, IV, pairs, D, rng, iters, deadline):
    """Anneal voltages on the darts `pairs` (list of (i, j)) to reach zero bad pairs."""
    gs = [rng.randrange(N) for _ in pairs]

    def darts_of(vals):
        return [(i, j, g) for (i, j), g in zip(pairs, vals)]

    cur = _cost(N, T, IV, darts_of(gs), D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        idx = rng.randrange(len(pairs))
        c = rng.randrange(N)
        if c == gs[idx]:
            continue
        old = gs[idx]
        gs[idx] = c
        v = _cost(N, T, IV, darts_of(gs), D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[idx] = old
    return darts_of(gs) if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N with a random 2+2 base; return (darts, T) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        IV = [inv(g) for g in range(N)]
        p = rng.randint(1, d - 1)
        M = [[p, d - p], [d - p, p]]
        pairs = [(i, j) for i in range(2) for j in range(2) for _ in range(M[i][j])]
        darts = _anneal(N, T, IV, pairs, D, rng, ITERS, deadline)
        if darts is not None:
            return darts, T
    return None


def _lift_edges(N, T, darts):
    """Edge list of the 4N-vertex lift; A_{i,x} = i*N + x, B_{j,y} = 2N + j*N + y."""
    N2 = 2 * N
    s = set()
    for i, j, g in darts:
        for x in range(N):
            s.add((i * N + x, N2 + j * N + T[x][g]))
    return 4 * N, sorted(s)


def _search(d, D, rng, deadline, best_n, consider):
    """Ascending search over lift orders N, keeping the best valid lift found."""
    Nmax = lib._moore_bound(d, D) // 4
    lo = max(d + 1, best_n // 4 + 1)
    pending = list(range(lo, Nmax + 1))
    if not pending:
        return
    budget = 0.3
    while pending and time.monotonic() < deadline:
        success = False
        for N in pending[:WINDOW]:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            darts, T = res
            n, e = _lift_edges(N, T, darts)
            consider(n, e)
            pending = [M for M in pending if M > N]
            success = True
            break
        if not success:
            budget *= 1.5


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + SAFETY * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Record-matching case for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        try:
            n, e = lib.projective_plane_incidence(d - 1)
            consider(n, e)
        except Exception:
            pass
        return best

    # Araujo-Pardo & Lopez family for D = 3 when d-2 is a prime power >= 3.
    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except Exception:
            pass

    try:
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
    except Exception:
        pass

    if d >= 2 and D >= 2 and time.monotonic() < deadline:
        try:
            _search(d, D, rng, deadline, best[0], consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
