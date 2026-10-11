import itertools
import math
import random
import time

import lib

ITERS_V = 600        # annealing steps per (group, split) try in the 4-base-vertex family
GROUP_LIMIT = 12     # groups tried per (order N, split) attempt
ITERS = 800          # annealing steps per try in the bi-Cayley fallback
MAX_GROUPS_PER_ATTEMPT = 30
TOP_SLACK = 8
TIME_FRAC = 0.8      # fraction of time_limit actually used
PHASE1_FRAC = 0.6    # fraction of time_limit for the new family


# ----------------------------------------------------------------------------
# Classical baselines (always valid when they pass lib.is_valid).
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
# NEW FAMILY: 2-by-2 voltage lifts over semidirect products Z_m x| Z_k.
#
# Base graph: A0, A1 (one side), B0, B1 (other side). Each A_i has degree d.
# With a00 = c, the forced multiplicities are a01 = a10 = d - c, a11 = c.
# Each base pair (A_i, B_j) carries a set V_ij of distinct group voltages.
# Lift vertices: A_i,x = i*N + x and B_j,y = (2+j)*N + y.
# Edges: A_i,x -- B_j,(x*v) for v in V_ij. Left multiplication by G is an
# automorphism, so eccentricities depend only on the base vertex, and four
# BFS sources (x = identity in each block) decide the diameter.
# Order 4N, bipartite and simple by construction.
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


def _lift_adj(N, Tm, V):
    """Adjacency lists of the 4N-vertex lift for voltage sets V (index 2*i + j)."""
    adj = [[] for _ in range(4 * N)]
    for i in range(2):
        for j in range(2):
            Vl = V[2 * i + j]
            bo = (2 + j) * N
            for x in range(N):
                a = i * N + x
                row = Tm[x]
                for v in Vl:
                    b = bo + row[v]
                    adj[a].append(b)
                    adj[b].append(a)
    return adj


def _unreach_from(adj, total, src, D):
    """Number of vertices not within distance D of src."""
    seen = bytearray(total)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        cnt += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return total - cnt


def _energy4(N, adj, D):
    """Total unreached pairs from the four base-vertex sources."""
    total = 4 * N
    return sum(_unreach_from(adj, total, src, D) for src in (0, N, 2 * N, 3 * N))


def _edges4(N, Tm, V):
    """Edge list of the lift."""
    edges = []
    for i in range(2):
        for j in range(2):
            bo = (2 + j) * N
            for x in range(N):
                a = i * N + x
                for v in V[2 * i + j]:
                    edges.append((a, bo + Tm[x][v]))
    return edges


def _anneal4(N, Tm, c, d, D, rng, iters, deadline):
    """Anneal voltage sets for the split c (a00 = a11 = c, a01 = a10 = d - c)."""
    sizes = [c, d - c, d - c, c]
    V = [rng.sample(range(N), s) for s in sizes]
    adj = _lift_adj(N, Tm, V)
    cur = _energy4(N, adj, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        p = rng.randrange(4)
        idx = rng.randrange(sizes[p])
        g = rng.randrange(N)
        if g in V[p]:
            continue
        old = V[p][idx]
        V[p][idx] = g
        adj2 = _lift_adj(N, Tm, V)
        val = _energy4(N, adj2, D)
        if val <= cur or rng.random() < math.exp(-(val - cur) / temp):
            cur, adj = val, adj2
        else:
            V[p][idx] = old
    return V if cur == 0 else None


def _attempt4(N, d, c, D, rng, deadline):
    """Try groups of order N for split c; return an edge list with diameter <= D, or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUP_LIMIT]:
        if time.monotonic() > deadline:
            return None
        order, mul, _ = lib.semidirect_group(m, k, r)
        Tm = [[mul(x, g) for g in range(N)] for x in range(N)]
        V = _anneal4(N, Tm, c, d, D, rng, ITERS_V, deadline)
        if V is not None:
            return _edges4(N, Tm, V)
    return None


# ----------------------------------------------------------------------------
# FALLBACK FAMILY: bi-Cayley graphs over Z_m x| Z_k (single base edge pair).
# ----------------------------------------------------------------------------

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
    """Try groups of order N for bi-Cayley graphs; return (T, S) or None."""
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


def _bicayley_search(d, D, rng, consider, deadline):
    """Fallback search over bi-Cayley graphs with decreasing budget per order."""
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
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

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + TIME_FRAC * time_limit
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

    if d == 1:
        consider(2, [(0, 1)])
        return best

    # Calibration shortcut: Moore graph for D = 3 when d - 1 is a prime power.
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

    # Phase 1: 4-vertex base voltage lifts (new construction).
    phase1_deadline = start + PHASE1_FRAC * time_limit
    Nmax4 = lib._moore_bound(d, D) // 4
    cur = max(d + 1, best_n // 4 + 1)
    budget = 2.0
    fails = 0
    while cur <= Nmax4 and time.monotonic() < phase1_deadline:
        c = rng.randint(1, d // 2)
        att_deadline = min(phase1_deadline, time.monotonic() + budget)
        edges = _attempt4(cur, d, c, D, rng, att_deadline)
        if edges is not None:
            consider(4 * cur, edges)
            cur += 1
            budget = 2.0
            fails = 0
        else:
            fails += 1
            if fails % 4 == 0:
                budget = min(budget * 1.5, 20.0)

    # Phase 2: bi-Cayley fallback with the remaining time.
    if time.monotonic() < deadline:
        _bicayley_search(d, D, rng, consider, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
