import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (order, base) within one attempt
ITERS = 400                   # annealing steps per bi-Cayley (group, connection set) try
ITERS_LIFT = 1500             # annealing steps per voltage-lift (group, voltages) try
AVALS = (2, 3)                # base sizes a: each lift has 2a base vertices (4 or 6)


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
# Shared group helpers.
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


def _groups_pref_noncyclic(N, rng):
    """Groups of order N, non-cyclic (k > 1) first, each part shuffled."""
    gs = _groups(N)
    nc = [g for g in gs if g[1] > 1]
    cy = [g for g in gs if g[1] == 1]
    rng.shuffle(nc)
    rng.shuffle(cy)
    return nc + cy


# ----------------------------------------------------------------------------
# Family A: bi-Cayley graphs (one base vertex per side), the parent's search.
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


def _bicayley_phase(d, D, rng, deadline, consider):
    """Parent's bi-Cayley search: keeps the 336 record path as a safe baseline."""
    if d < 2 or D < 2:
        return
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


# ----------------------------------------------------------------------------
# Family B (bold change): voltage lifts of a regular bipartite base multigraph
# with a base vertices per side (2a vertices total), over NON-cyclic groups.
# Lift order = 2a * N. Left multiplication by the group is an automorphism,
# so checking eccentricity from one vertex per base vertex suffices.
# ----------------------------------------------------------------------------

def _base_darts(a, d, rng):
    """Random connected d-regular bipartite base multigraph on a+a vertices, as a list of (i, j) darts."""
    for _ in range(100):
        perms = [rng.sample(range(a), a) for _ in range(d)]
        parent = list(range(2 * a))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for p in perms:
            for i in range(a):
                parent[find(i)] = find(a + p[i])
        if len({find(x) for x in range(2 * a)}) == 1:
            return [(i, p[i]) for p in perms for i in range(a)]
    return None


def _lift_cost(V, N, T, adj, D):
    """Sum over base sources of unreached (vertex) counts within distance D."""
    NV = V * N
    total = 0
    for src in range(V):
        seen = bytearray(NV)
        s = src * N
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                b, x = divmod(u, N)
                row = T[x]
                for vb, g in adj[b]:
                    w = vb * N + row[g]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += NV - count
    return total


def _build_adj(V, a, base, vol, invs):
    """Adjacency per base vertex: A base i -> (a+j, h); B base a+j -> (i, h^-1)."""
    adj = [[] for _ in range(V)]
    for (i, j), h in zip(base, vol):
        adj[i].append((a + j, h))
        adj[a + j].append((i, invs[h]))
    return adj


def _lift_anneal(a, d, D, N, T, invs, rng, iters, deadline):
    """Anneal voltages on a random base so the lift has diameter <= D. Returns darts or None."""
    base = _base_darts(a, d, rng)
    if base is None:
        return None
    V = 2 * a
    nd = len(base)
    vol = [0] * nd
    for k in range(nd):
        used = {vol[t] for t in range(k) if base[t] == base[k]}
        h = rng.randrange(N)
        while h in used:
            h = rng.randrange(N)
        vol[k] = h
    cur = _lift_cost(V, N, T, _build_adj(V, a, base, vol, invs), D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        k = rng.randrange(nd)
        used = {vol[t] for t in range(nd) if t != k and base[t] == base[k]}
        if len(used) >= N:
            continue
        h = rng.randrange(N)
        while h in used:
            h = rng.randrange(N)
        old = vol[k]
        vol[k] = h
        temp = max(0.2, 2.0 * (1.0 - it / iters))
        v = _lift_cost(V, N, T, _build_adj(V, a, base, vol, invs), D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            vol[k] = old
    if cur == 0:
        return [(base[k][0], base[k][1], vol[k]) for k in range(nd)]
    return None


def _lift_attempt(a, d, D, N, rng, deadline):
    """Try non-cyclic (then cyclic) groups of order N for a valid voltage lift."""
    groups = _groups_pref_noncyclic(N, rng)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _lift_anneal(a, d, D, N, T, invs, rng, ITERS_LIFT, deadline)
        if darts is not None:
            return darts, T
    return None


def _lift_edges(a, N, T, darts):
    """Expand darts (i, j, h) into the full edge list of the lift."""
    edges = []
    for i, j, h in darts:
        for x in range(N):
            edges.append((i * N + x, (a + j) * N + T[x][h]))
    return edges


def _lift_phase(d, D, rng, deadline, consider, best_n):
    """Search lifts with orders above the current best, one N-pointer per base size."""
    bound = lib._moore_bound(d, D)
    ptr = {}
    for a in AVALS:
        ptr[a] = max(best_n() // (2 * a) + 1, 2)
    budget = 1.5
    while time.monotonic() < deadline:
        if all(ptr[a] > bound // (2 * a) for a in AVALS):
            break
        progressed = False
        for a in AVALS:
            V = 2 * a
            if time.monotonic() >= deadline:
                break
            ptr[a] = max(ptr[a], best_n() // V + 1)
            if ptr[a] > bound // V:
                continue
            N = ptr[a]
            now = time.monotonic()
            att_deadline = min(deadline, now + budget)
            res = _lift_attempt(a, d, D, N, rng, att_deadline)
            if res is None:
                continue
            darts, T = res
            edges = _lift_edges(a, N, T, darts)
            consider(V * N, edges)
            ptr[a] = N + 1
            progressed = True
        if not progressed:
            budget *= 2


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)
    tl = max(float(time_limit), 1.0)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    def best_n():
        return best[0]

    try:
        # Record-matching case: incidence graph of PG(2, d-1).
        if D == 3 and lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            consider(n, e)
            return best[0], best[1]

        if D >= 2:
            consider(*lib.haar_graph(d, range(d)))
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        if D >= 4 and time.monotonic() < start + 0.2 * tl:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
    except Exception:
        pass

    if d < 2 or D < 2:
        return best[0], best[1]

    # Phase 1: parent's bi-Cayley search (safe baseline, roughly the record).
    try:
        _bicayley_phase(d, D, rng, start + 0.35 * tl, consider)
    except Exception:
        pass

    # Phase 2: bold change, voltage lifts over non-cyclic groups with 4 or 6 base vertices.
    try:
        _lift_phase(d, D, rng, start + 0.78 * tl, consider, best_n)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
