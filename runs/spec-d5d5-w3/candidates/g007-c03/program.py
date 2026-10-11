import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one attempt
ITERS = 800                   # annealing steps per restart
RESTARTS = 4                  # fresh random connection sets per group before moving on
TOP_SLACK = 8                 # search orders up to Nmax//2 + TOP_SLACK

LIFT_GROUPS = 12              # groups tried per order N in the bold lift search
LIFT_ITERS = 600              # annealing steps per lift restart
LIFT_RESTARTS = 2
LIFT_BUDGET = 0.6             # seconds per order N in the lift scan
BICAYLEY_SHARE = 0.3          # fraction of the usable time kept for the safe bi-Cayley search


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
# Safe family: bi-Cayley search over semidirect products Z_m x| Z_k of order N.
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
    """Try groups of order N; for each group run several independent annealing restarts."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                return None
            S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
            if S is not None:
                return T, S
    return None


def _bicayley(d, D, rng, top, Nmax, deadline, consider):
    """Safe search: bi-Cayley graphs with N descending from top, budget growing on failure."""
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
            budget *= 1.5


# ----------------------------------------------------------------------------
# Bold family: 2x2-base voltage lifts over finite groups.
#
# Base: A_0, A_1, B_0, B_1 with multiplicities c[i][j] (row and column sums d).
# Vertices: A_i x -> i*N + x ; B_j y -> 2N + j*N + y.  Dart (i, j, g) joins
# A_i x to B_j (x*g). Left multiplication is an automorphism, so one source per
# fiber (4 total) decides the diameter. Unlike the bi-Cayley family, this has
# 4N vertices and a two-vertex-per-side base with free per-pair voltage sets.
# ----------------------------------------------------------------------------

def _flat(sets):
    return [(i, j, g) for (i, j), gs in sets.items() for g in gs]


def _lift_unreached(N, mul_tab, darts, D):
    """Count (source, vertex) pairs not within distance D for the four fiber sources."""
    n = 4 * N
    adj = [[] for _ in range(n)]
    for i, j, g in darts:
        ai = i * N
        bj = 2 * N + j * N
        for x in range(N):
            a = ai + x
            b = bj + mul_tab[x][g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += n - count
    return total


def _lift_anneal(N, mul_tab, sets, D, rng, iters, deadline):
    """Anneal the voltage sets (distinct elements per pair) to zero unreached pairs."""
    cur = _lift_unreached(N, mul_tab, _flat(sets), D)
    keys = list(sets.keys())
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        key = keys[rng.randrange(len(keys))]
        gs = sets[key]
        idx = rng.randrange(len(gs))
        new = rng.randrange(N)
        if new in gs:
            continue
        old = gs[idx]
        gs[idx] = new
        v = _lift_unreached(N, mul_tab, _flat(sets), D)
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[idx] = old
    return cur == 0


def _lift_edges(N, mul_tab, sets):
    edges = []
    for (i, j), gs in sets.items():
        for g in gs:
            for x in range(N):
                edges.append((i * N + x, 2 * N + j * N + mul_tab[x][g]))
    return edges


def _lift_try(N, d, D, rng, deadline):
    """Try to find a valid 4N-vertex lift of order N; return its edge list or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    counts = [a for a in range(1, d) if a <= d - a]
    for m, k, r in groups[:LIFT_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        mul_tab = [[mul(x, g) for g in range(N)] for x in range(N)]
        for a in counts:
            c = {(0, 0): a, (0, 1): d - a, (1, 0): d - a, (1, 1): a}
            for _ in range(LIFT_RESTARTS):
                if time.monotonic() > deadline:
                    return None
                sets = {key: rng.sample(range(N), cnt)
                        for key, cnt in c.items() if cnt > 0}
                if _lift_anneal(N, mul_tab, sets, D, rng, LIFT_ITERS, deadline):
                    return _lift_edges(N, mul_tab, sets)
    return None


def _lift_search(d, D, rng, deadline, consider, best_n):
    """Bold search: scan N upward from the first order that beats best_n."""
    Nmax = lib._moore_bound(d, D) // 4   # 4N vertices must fit the Moore bound
    N = best_n // 4 + 1
    while N <= Nmax and time.monotonic() < deadline:
        ddl = min(deadline, time.monotonic() + LIFT_BUDGET)
        edges = _lift_try(N, d, D, rng, ddl)
        if edges is not None:
            consider(4 * N, edges)
        N += 1


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

    # Record-matching case: incidence graph of PG(2, d-1).
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

    # Safe baseline first, so a valid strong graph is secured early.
    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
    usable = deadline - start
    bi_deadline = start + BICAYLEY_SHARE * usable
    try:
        _bicayley(d, D, rng, top, Nmax, bi_deadline, consider)
    except Exception:
        pass

    # Bold search: 2x2-base lifts over finite groups, using the remaining time.
    if d >= 3 and D >= 4 and time.monotonic() < deadline:
        try:
            _lift_search(d, D, rng, deadline, consider, best_n)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
