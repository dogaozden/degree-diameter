import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base construction: generalized quadrangle W(q) incidence graph (diameter 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); bipartite, diameter 4, degree q+1."""
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


# ----------------------------------------------------------------------------
# Bold new construction: bi-Cayley graphs over a group G (one vertex per side
# per group element). Vertices a_g (index g) and b_h (index G+h); a_g ~ b_{g*s}
# for s in S, |S| = d. Left multiplication is an automorphism, so the graph has
# diameter <= D iff BFS from a_e and from b_e reaches everything within D.
# A simulated-annealing search picks S to minimize unreached pairs.
# ----------------------------------------------------------------------------

def _group_tables(G, rng):
    """Return (mul_table, inverse_list) for a cyclic or random semidirect group of order G."""
    built = None
    if rng.random() < 0.5:
        ks = [k for k in range(2, 13) if G % k == 0 and G // k >= 2]
        rng.shuffle(ks)
        for k2 in ks[:3]:
            m = G // k2
            rs = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                  if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if rs:
                try:
                    built = lib.semidirect_group(m, k2, rng.choice(rs))
                except ValueError:
                    built = None
                if built is not None:
                    break
    if built is None:
        built = lib.cyclic_group(G)
    order, mul, inv = built
    table = [[mul(x, y) for y in range(G)] for x in range(G)]
    invs = [inv(x) for x in range(G)]
    return table, invs


def _cost(G, table, invs, S, D):
    """Unreached pairs from a_e and b_e within distance D (zero iff diameter <= D)."""
    N = 2 * G
    adj = [None] * N
    for g in range(G):
        row = table[g]
        adj[g] = [G + row[s] for s in S]
    for h in range(G):
        row = table[h]
        adj[G + h] = [row[invs[s]] for s in S]
    total = 0
    for src in (0, G):
        seen = bytearray(N)
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
        total += N - cnt
    return total


def _search(G, table, invs, d, D, rng, deadline):
    """Anneal a d-element connection set S until the bi-Cayley graph has diameter <= D."""
    S = rng.sample(range(G), d)
    cost = _cost(G, table, invs, S, D)
    while cost > 0:
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        S2 = list(S)
        S2[i] = new
        c2 = _cost(G, table, invs, S2, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / 0.7):
            S, cost = S2, c2
    return S


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.80 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    # D = 3: projective plane incidence when d-1 is a prime power.
    if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        if best[0] >= moore:
            return best

    # D = 4: generalized quadrangle base (small q keeps construction fast).
    if D == 4:
        qs = [q for q in range(min(d - 1, 7), 1, -1) if lib.is_prime_power(q)]
        if qs and time.monotonic() < start + 0.2 * T:
            consider(*_gq_w(qs[0]))

    # Bi-Cayley search: order G of the group; vertex count 2G.
    hi = min(moore // 2, 600)
    lo = max(d, best[0] // 2 + 1)
    while time.monotonic() < deadline and lo <= hi:
        G = min(hi, lo + rng.randrange(0, 8))
        remaining = deadline - time.monotonic()
        if remaining <= 0.2:
            break
        attempt_deadline = time.monotonic() + min(remaining, 3.0)
        table, invs = _group_tables(G, rng)
        S = _search(G, table, invs, d, D, rng, attempt_deadline)
        if S is not None:
            edges = [(g, G + table[g][s]) for g in range(G) for s in S]
            consider(2 * G, edges)
            lo = max(lo, G + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
