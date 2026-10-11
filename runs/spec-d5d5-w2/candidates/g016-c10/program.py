import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines: projective planes (D = 3) and the generalized
# quadrangle W(q) (D = 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Points and lines of the generalized quadrangle W(q) as a bipartite graph (diameter 4)."""
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

    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k with hill-climbed connection sets.
# ----------------------------------------------------------------------------

MAX_GROUPS = 8
CLIMB_ITERS = 300
_TABLE_CACHE = {}


def _groups(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Pairs (source, target) not within distance D, from A_0 and B_0 (bi-Cayley symmetry)."""
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


def _climb(N, T, invs, d, D, rng, iters, deadline):
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur:
            S, cur = S2, v
    return S if cur == 0 else None


def _bicayley_sweep(d, D, rng, deadline, lo):
    """Sweep the bi-Cayley order N upward from lo; return (N, edges) for the largest success."""
    best = None
    N = lo
    while time.monotonic() < deadline:
        groups = _groups(N)
        rng.shuffle(groups)
        hit = None
        for m, k2, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            _, _, T, invs = _tables(m, k2, r)
            S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
            if S is not None:
                hit = (T, S)
                break
        if hit is None:
            break
        T, S = hit
        edges = [(x, N + T[x][g]) for x in range(N) for g in S]
        best = (N, edges)
        N += 1
    return best


# ----------------------------------------------------------------------------
# NEW: vertex insertion into a d-regular bipartite graph, then repair by
# degree-preserving 2-switches with simulated annealing on the number of
# vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance > D, via bitset balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _replace(adj, E, i, new):
    """Replace edge index i of E (and adjacency) by the pair new = (a, b)."""
    a, b = E[i]
    adj[a].discard(b)
    adj[b].discard(a)
    na, nb = new
    adj[na].add(nb)
    adj[nb].add(na)
    E[i] = new


def _insert(n, adj, E, d, rng):
    """Add a new A-vertex n and a new B-vertex n+1 by rerouting a matching of d edges.

    Each rerouted edge (a_i, b_i) becomes (a_i, n+1) and (n, b_i), so every degree stays d.
    Returns (n+2, adj, E) or None if no suitable matching was found.
    """
    order = list(range(len(E)))
    rng.shuffle(order)
    used_a, used_b, chosen = set(), set(), []
    for idx in order:
        a, b = E[idx]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(idx)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    adj2 = [set(s) for s in adj] + [set(), set()]
    na, nb = n, n + 1
    cs = set(chosen)
    E2 = [E[i] for i in range(len(E)) if i not in cs]
    for idx in chosen:
        a, b = E[idx]
        adj2[a].discard(b)
        adj2[b].discard(a)
        adj2[na].add(b)
        adj2[b].add(na)
        adj2[a].add(nb)
        adj2[nb].add(a)
        E2.append((na, b))
        E2.append((a, nb))
    return n + 2, adj2, E2


def _anneal2(n, adj, E, D, rng, deadline):
    """Anneal degree-preserving 2-switches until no pair is farther than D. True on success."""
    cost = _bad_pairs(n, adj, D)
    M = len(E)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = 2.0
    it = 0
    while cost > 0:
        if time.monotonic() >= deadline:
            break
        it += 1
        if it % 32 == 0:
            frac = min(1.0, (time.monotonic() - t0) / span)
            T = 2.0 * (0.1 / 2.0) ** frac
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        old1, old2 = E[i], E[j]
        _replace(adj, E, i, (a1, b2))
        _replace(adj, E, j, (a2, b1))
        c2 = _bad_pairs(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _replace(adj, E, j, old2)
            _replace(adj, E, i, old1)
    return cost == 0


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.88 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D == 2:
        return best
    if d == 2:
        n = 2 * D  # even cycle of length 2D has diameter D and is bipartite
        return n, [(i, (i + 1) % n) for i in range(n)]

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best[0] < moore:
        # Phase 1: regular bi-Cayley base graph.
        base_deadline = start + 0.4 * budget
        lo = max(d, best[0] // 2 + 1)
        found = _bicayley_sweep(d, D, rng, base_deadline, lo)
        if found is not None:
            N, edges = found
            consider(2 * N, edges)

            # Phase 2: grow the d-regular graph by vertex insertion + 2-switch repair.
            n = 2 * N
            E = list(edges)
            adj = [set() for _ in range(n)]
            for a, b in E:
                adj[a].add(b)
                adj[b].add(a)
            while time.monotonic() < deadline - 0.2 and best[0] < moore:
                rem = deadline - time.monotonic()
                slice_t = min(rem, max(2.0, 0.3 * rem))
                cand = _insert(n, adj, E, d, rng)
                if cand is None:
                    continue
                n2, adj2, E2 = cand
                if _anneal2(n2, adj2, E2, D, rng, time.monotonic() + slice_t):
                    edges2 = [(a, b) for a, b in E2]
                    if lib.is_valid(n2, edges2, d, D):
                        consider(n2, edges2)
                        n, adj, E = n2, adj2, E2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
