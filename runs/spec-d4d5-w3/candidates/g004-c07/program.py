import itertools
import math
import random
import time

import lib


# Fraction of time_limit spent in the search. The rest is margin.
FRAC = 0.85
ANNEAL_T = 0.5


# ----------------------------------------------------------------------------
# Seed graphs: d-regular bipartite graphs, A side = vertices 0..k-1, B side = k..2k-1.
# ----------------------------------------------------------------------------

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


def _seed(d, D):
    """Best valid d-regular bipartite seed among a few algebraic candidates."""
    cands = []
    if d == 4 and D >= 4:
        try:
            cands.append(_gq_w(3))
        except Exception:
            pass
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        try:
            cands.append(lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
    cands.append(lib.haar_graph(d, range(d)))  # K_{d,d}, diameter 2
    for n, e in cands:
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------
# Cost: number of unordered pairs at distance > D (bitset balls).
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _cost(k, E, D):
    n = 2 * k
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(k + b)
        adj[k + b].append(a)
    return _bad_pairs(n, adj, D)


# ----------------------------------------------------------------------------
# Edge-switch annealing that keeps the graph d-regular and bipartite.
# ----------------------------------------------------------------------------

def _anneal(k, E, Eset, D, deadline, rng):
    """Random 2-switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) with Metropolis acceptance on bad pairs."""
    cost = _cost(k, E, D)
    m = len(E)
    while cost > 0:
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in Eset or (a2, b1) in Eset:
            continue
        old_i, old_j = E[i], E[j]
        Eset.discard((a1, b1))
        Eset.discard((a2, b2))
        Eset.add((a1, b2))
        Eset.add((a2, b1))
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        c2 = _cost(k, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / ANNEAL_T):
            cost = c2
        else:
            Eset.discard((a1, b2))
            Eset.discard((a2, b1))
            Eset.add((a1, b1))
            Eset.add((a2, b2))
            E[i] = old_i
            E[j] = old_j
    return cost


def _grow(k, E, d, rng):
    """Add one A vertex k and one B vertex k: remove d matched edges and reattach them to the new pair.

    Degrees are preserved, and every vertex stays d-regular.
    """
    chosen = None
    for _ in range(200):
        idx = list(range(len(E)))
        rng.shuffle(idx)
        usedA, usedB, pick = set(), set(), []
        for t in idx:
            a, b = E[t]
            if a in usedA or b in usedB:
                continue
            usedA.add(a)
            usedB.add(b)
            pick.append(t)
            if len(pick) == d:
                break
        if len(pick) == d:
            chosen = pick
            break
    if chosen is None:
        return None
    cs = set(chosen)
    newE = [E[t] for t in range(len(E)) if t not in cs]
    for t in chosen:
        a, b = E[t]
        newE.append((k, b))
        newE.append((a, k))
    return newE


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + FRAC * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    best = None
    try:
        n0, e0 = _seed(d, D)
        best = (n0, list(e0))
        moore = lib.moore_bound(d, D)
        if n0 < moore:
            k = n0 // 2
            E = [(min(u, v), max(u, v) - k) for u, v in e0]
            while time.monotonic() < deadline and 2 * k < moore:
                Eset = set(E)
                cost = _anneal(k, E, Eset, D, deadline, rng)
                if cost != 0:
                    break
                n = 2 * k
                edges = [(a, k + b) for a, b in E]
                if n > best[0] and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                nextE = _grow(k, E, d, rng)
                if nextE is None:
                    break
                E = nextE
                k += 1
    except Exception:
        pass

    if best is None or not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
