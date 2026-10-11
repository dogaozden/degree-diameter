import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Projective plane base (used for small d, e.g. d = 3 where it meets the bound).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
# Vertices: A_i,g = i*G + g (indices < k*G), B_j,h = (k+j)*G + h.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _vcost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _vedges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and B-assignments of each layer."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _vcost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _vcost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _vcost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _vedges(k, G, darts, perms)
    return None


def _voltage_phase(d, D, st, rng, deadline, consider):
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = st["n"] // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, 400)
        if res is not None:
            consider(res[0], res[1])


# ----------------------------------------------------------------------------
# New family: edge-switch annealing with vertex insertion, warm-started from the
# best valid bipartite graph found so far.
#
# State: adjA[a] = list of B-local indices, adjB[b] = list of A-local indices.
# A-vertex a has global id a; B-vertex b has global id N + b.
# Degrees are preserved by switches and by insertion (each new vertex has
# degree d, and each endpoint of a removed edge keeps its degree).
# ----------------------------------------------------------------------------

def _bcost(adjA, adjB, D):
    """Ordered pairs at distance > D (zero means diameter <= D; graph is bipartite by design)."""
    N = len(adjA)
    n = 2 * N
    adj = [[N + b for b in adjA[a]] for a in range(N)]
    adj.extend(list(adjB[b]) for b in range(N))
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _rep(lst, old, new):
    lst[lst.index(old)] = new


def _apply(adjA, adjB, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1)."""
    _rep(adjA[a1], b1, b2)
    _rep(adjA[a2], b2, b1)
    _rep(adjB[b1], a1, a2)
    _rep(adjB[b2], a2, a1)


def _pick_switch(adjA, adjB, rng):
    N = len(adjA)
    a1 = rng.randrange(N)
    a2 = rng.randrange(N)
    if a1 == a2 or not adjA[a1] or not adjA[a2]:
        return None
    b1 = rng.choice(adjA[a1])
    b2 = rng.choice(adjA[a2])
    if b1 == b2 or b2 in adjA[a1] or b1 in adjA[a2]:
        return None
    return a1, b1, a2, b2


def _insert(adjA, adjB, d, rng):
    """Add one A-vertex and one B-vertex, each of degree d, by subdividing a d-matching."""
    N = len(adjA)
    if N < d:
        return False
    As = Bs = None
    for _ in range(200):
        cand_a = rng.sample(range(N), d)
        cand_b = []
        for a in cand_a:
            if not adjA[a]:
                break
            cand_b.append(rng.choice(adjA[a]))
        if len(cand_b) == d and len(set(cand_b)) == d:
            As, Bs = cand_a, cand_b
            break
    if As is None:
        return False
    newA = N
    newB = N
    for a, b in zip(As, Bs):
        _rep(adjA[a], b, newB)   # a loses b, gains new B-vertex
        _rep(adjB[b], a, newA)   # b loses a, gains new A-vertex
    adjA.append(list(Bs))        # new A-vertex joined to the b's
    adjB.append(list(As))        # new B-vertex joined to the a's
    return True


def _sa_repair(adjA, adjB, D, rng, deadline, max_iter):
    cost = _bcost(adjA, adjB, D)
    it = 0
    while cost > 0 and it < max_iter:
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        it += 1
        mv = _pick_switch(adjA, adjB, rng)
        if mv is None:
            continue
        a1, b1, a2, b2 = mv
        _apply(adjA, adjB, a1, b1, a2, b2)
        c2 = _bcost(adjA, adjB, D)
        T = max(0.2, 1.5 * (1.0 - it / max_iter))
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _apply(adjA, adjB, a1, b2, a2, b1)
    return cost


def _to_edges(adjA):
    N = len(adjA)
    return 2 * N, [(a, N + b) for a in range(N) for b in adjA[a]]


def _warm_growth(d, D, st, rng, deadline, consider):
    n, e = st["n"], st["e"]
    if n % 2:
        return
    N = n // 2
    if N < d:
        return
    adjA = [[] for _ in range(N)]
    adjB = [[] for _ in range(N)]
    for u, v in e:
        a, b = min(u, v), max(u, v)
        if not (a < N <= b):
            return
        adjA[a].append(b - N)
        adjB[b - N].append(a)

    snapA, snapB = adjA, adjB
    while time.monotonic() < deadline:
        curA = [list(x) for x in snapA]
        curB = [list(x) for x in snapB]
        if not _insert(curA, curB, d, rng):
            continue
        if _sa_repair(curA, curB, D, rng, deadline, 1500) == 0:
            snapA, snapB = curA, curB
            n2, e2 = _to_edges(curA)
            if n2 > st["n"]:
                consider(n2, e2)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.8 * time_limit
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    base_n, base_e = lib.haar_graph(d, range(d))
    st = {"n": base_n, "e": base_e}
    if st["n"] >= lib._moore_bound(d, D):
        return st["n"], st["e"]

    def consider(n, e):
        if n > st["n"] and lib.is_valid(n, e, d, D):
            st["n"], st["e"] = n, list(e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if st["n"] >= lib._moore_bound(d, D):
            return st["n"], st["e"]

    # Phase 1: voltage lifts (produces the structured starting point).
    # Phase 2: edge-switch + vertex-insertion growth from the best graph.
    vdl = start + 0.4 * total if D >= 3 else deadline
    _voltage_phase(d, D, st, rng, vdl, consider)

    if D >= 3 and time.monotonic() < deadline:
        _warm_growth(d, D, st, rng, deadline, consider)

    if not lib.is_valid(st["n"], st["e"], d, D):
        return lib.haar_graph(d, range(d))
    return st["n"], st["e"]
