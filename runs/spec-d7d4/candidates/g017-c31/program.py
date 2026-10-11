import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over semidirect products G = Z_m x| Z_k.
#
# Group elements (a, b) are coded as a*k + b with product
#     (a, b)(c, d) = (a + r^b c, b + d),
# which is associative when r^k = 1 mod m and gcd(r, m) = 1. The identity is 0.
#
# Graph: A-vertices g and B-vertices h (indices G + h), with A_g ~ B_{g s} for s in S.
# Left translation is an automorphism, so distances from A_e and B_e suffice:
# the graph has diameter <= D iff both sources reach everything within D.
# Right-multiplying S by s0^{-1} gives the same graph, so WLOG e is in S.
# ----------------------------------------------------------------------------

def _semidirect_table(m, k, r):
    G = m * k
    pw = [pow(r, b, m) for b in range(k)]
    mt = []
    for x in range(G):
        a, b = divmod(x, k)
        pb = pw[b]
        row = [0] * G
        for y in range(G):
            c, dd = divmod(y, k)
            row[y] = ((a + pb * c) % m) * k + (b + dd) % k
        mt.append(row)
    return mt


def _inverses(mt):
    # Identity is 0, so the inverse of x is the y with x*y = 0.
    return [row.index(0) for row in mt]


def _groups_of_order(G, rng):
    out = []
    for k in range(1, G):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:3]:
            out.append((m, k, r))
    rng.shuffle(out)
    return out


def _cost(G, S, mt, inv, D):
    """Number of (source, vertex) pairs at distance > D, over sources A_e and B_e."""
    invS = [inv[s] for s in S]
    total = 0
    for side in (0, 1):
        seen = [bytearray(G), bytearray(G)]  # seen[0] = A side, seen[1] = B side
        seen[side][0] = 1
        frontier = [(side, 0)]
        count = 1
        for _ in range(D):
            nxt = []
            for t, x in frontier:
                row = mt[x]
                if t == 0:
                    targets, tgt, nt = S, seen[1], 1
                else:
                    targets, tgt, nt = invS, seen[0], 0
                for s in targets:
                    y = row[s]
                    if not tgt[y]:
                        tgt[y] = 1
                        nxt.append((nt, y))
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * G - count
    return total


def _anneal(G, d, D, mt, inv, rng, deadline):
    """Simulated annealing over the connection set S (size d, containing identity 0)."""
    if d > G or d < 2:
        return None
    others = list(range(1, G))
    S = [0] + rng.sample(others, d - 1)
    cur = _cost(G, S, mt, inv, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 1.5 * (0.02 ** ((now - t0) / span))
        i = rng.randrange(1, d)
        cand = rng.randrange(1, G)
        if cand in S:
            continue
        old = S[i]
        S[i] = cand
        c2 = _cost(G, S, mt, inv, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
        else:
            S[i] = old
    return list(S) if cur == 0 else None


def _graph_from(G, S, mt):
    edges = [(g, G + mt[g][s]) for g in range(G) for s in S]
    return 2 * G, edges


def _bicayley_search(d, D, deadline, rng, consider):
    """Climb the group order G upward, annealing a connection set for each."""
    G = max(d, lib._moore_bound(d, D) // 4)
    fails = 0
    while time.monotonic() < deadline and fails < 6:
        groups = _groups_of_order(G, rng)[:4]
        if not groups:
            fails += 1
            G += 1
            continue
        per_group = min(deadline - time.monotonic(), 4.0) / len(groups)
        found = None
        for m, k, r in groups:
            now = time.monotonic()
            if now >= deadline:
                break
            mt = _semidirect_table(m, k, r)
            inv = _inverses(mt)
            S = _anneal(G, d, D, mt, inv, rng,
                        min(deadline, now + per_group))
            if S is not None:
                found = (mt, S)
                break
        if found is not None:
            mt, S = found
            n, edges = _graph_from(G, S, mt)
            consider(n, edges)
            fails = 0
        else:
            fails += 1
        G += 1


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if best[0] >= lib._moore_bound(d, D):
        return best

    # D = 3: projective plane incidence graph (meets the Moore bound when d-1 is a prime power).
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best[0] >= lib._moore_bound(d, D):
            return best

    # Main construction: bi-Cayley graphs over semidirect products, one orbit per side.
    _bicayley_search(d, D, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
