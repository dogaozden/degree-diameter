import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order N within one attempt
ITERS = 400                   # annealing steps per (group, connection set) try

K2 = 2                        # base graph has K2 vertices per side (new construction)


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
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
# Bi-Cayley search over semidirect products Z_m x| Z_k of order N (legacy).
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


def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _legacy_build(d, D, seed, time_limit):
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

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2 and d >= 1:
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

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + 3)
    cands = set(range(d + 1, top + 1))

    budget = 0.4
    while time.monotonic() < deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best


# ----------------------------------------------------------------------------
# NEW construction: 2-vertex-per-side base graph lifted over a group G.
#
# Vertices A_{i,x} = i*N + x (i in {0,1}), B_{j,y} = (2+j)*N + y.
# Each base cell (i, j) carries a set of distinct labels g in G; the lift has
# edges A_{i,x} -- B_{j, x*g}. Cell counts (a, d-a, d-a, a) make every vertex
# have degree exactly d. Left multiplication by G is an automorphism, so the
# diameter condition only needs BFS from the 2K representatives A_{i,e}, B_{j,e}.
# ----------------------------------------------------------------------------

def _k2_outlists(lab, invs):
    outA = [[] for _ in range(K2)]
    inB = [[] for _ in range(K2)]
    for (i, j), gs in lab.items():
        for g in gs:
            outA[i].append((j, g))
            inB[j].append((i, invs[g]))
    return outA, inB


def _k2_cost(N, D, T, outA, inB):
    """Number of (source, vertex) pairs not within distance D, over the 2K representatives."""
    V = 2 * K2 * N
    kN = K2 * N
    sources = [i * N for i in range(K2)] + [kN + j * N for j in range(K2)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outA[i]:
                        v = kN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    row = T[y]
                    for i, h in inB[j]:
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


def _k2_anneal(N, D, d, a, T, invs, rng, iters, deadline):
    """Anneal the dart labels for fixed cell counts (a, d-a, d-a, a) until the lift has diameter <= D."""
    lab = {
        (0, 0): rng.sample(range(N), a),
        (0, 1): rng.sample(range(N), d - a),
        (1, 0): rng.sample(range(N), d - a),
        (1, 1): rng.sample(range(N), a),
    }
    outA, inB = _k2_outlists(lab, invs)
    cur = _k2_cost(N, D, T, outA, inB)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        key = rng.choice(list(lab.keys()))
        gs = lab[key]
        idx = rng.randrange(len(gs))
        c = rng.randrange(N)
        if c in gs:
            continue
        old = gs[idx]
        gs[idx] = c
        outA2, inB2 = _k2_outlists(lab, invs)
        v = _k2_cost(N, D, T, outA2, inB2)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[idx] = old
    if cur == 0:
        return {k: list(v) for k, v in lab.items()}
    return None


def _k2_search(d, D, rng, deadline, lo):
    """Search group orders N in [lo, Nmax] for a K2-vertex-per-side lift with diameter <= D."""
    Nmax = lib._moore_bound(d, D) // (2 * K2)
    best = None
    while time.monotonic() < deadline and lo <= Nmax:
        N = rng.randint(lo, Nmax)
        groups = _groups(N)
        if not groups:
            continue
        attempt_end = min(deadline, time.monotonic() + 3.0)
        found = None
        while time.monotonic() < attempt_end and found is None:
            mm, kk, rr = rng.choice(groups)
            order, mul, inv = lib.semidirect_group(mm, kk, rr)
            T = [[mul(x, g) for g in range(N)] for x in range(N)]
            invs = [inv(g) for g in range(N)]
            a = rng.randint(1, d - 1)
            found = _k2_anneal(N, D, d, a, T, invs, rng, 600, attempt_end)
            if found is not None:
                best = (N, T, found)
        if found is not None:
            lo = N + 1
    return best


def _k2_edges(N, T, lab):
    kN = K2 * N
    edges = []
    for (i, j), gs in lab.items():
        for g in gs:
            for x in range(N):
                edges.append((i * N + x, kN + j * N + T[x][g]))
    return 2 * K2 * N, edges


def _build_d5d5(d, D, seed, rng, start, time_limit):
    deadline = start + 0.7 * time_limit
    best_n, best_e = 1, []

    res = _k2_search(d, D, rng, deadline, lo=85)   # 4*85 = 340 > 336 record
    if res is not None:
        N, T, lab = res
        n, e = _k2_edges(N, T, lab)
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if best_n <= 336:
        remaining = time_limit - (time.monotonic() - start)
        n, e = _legacy_build(d, D, seed, max(0.5, remaining * 0.85))
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []
    return best_n, best_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)
    if d < 1 or D < 1:
        return 1, []
    if d == 5 and D == 5:
        return _build_d5d5(d, D, seed, rng, start, time_limit)
    return _legacy_build(d, D, seed, time_limit)
