import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over small groups, searched by hill-climbing on the set S.
#
# Vertices: A_g = g and B_h = G + h, for g, h in a group H of order G.
# Edges: A_g -- B_{g*s} for s in S, |S| = d. Left multiplication by H is an
# automorphism preserving both sides, so distances from A_e and B_e suffice.
# The groups come from two families: random permutation groups (closure of two
# random permutations, capped in order) and semidirect products Z_m x| Z_k.
# ----------------------------------------------------------------------------


def _perm_group(lo, hi, rng):
    """Random 2-generated permutation group with order in [lo, hi]; returns (G, table, inv) or None."""
    m = rng.randint(4, 8)

    def rand_perm():
        p = list(range(m))
        rng.shuffle(p)
        return tuple(p)

    gens = [rand_perm(), rand_perm()]
    e = tuple(range(m))
    elems = [e]
    idx = {e: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = tuple(x[j] for j in g)
            if y not in idx:
                if len(elems) >= hi:
                    return None
                idx[y] = len(elems)
                elems.append(y)
    G = len(elems)
    if G < lo or G > hi:
        return None
    table = [[idx[tuple(elems[a][elems[b][j]] for j in range(m))] for b in range(G)]
             for a in range(G)]
    inv = [0] * G
    for a in range(G):
        row = table[a]
        for b in range(G):
            if row[b] == 0:
                inv[a] = b
                break
    return G, table, inv


def _semi_group(G, rng):
    """Random semidirect product Z_m x| Z_k of order G; returns (G, table, inv) or None."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    k = rng.choice(divs)
    m = G // k
    r = 1
    if k > 1:
        ok = False
        for _ in range(40):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                ok = True
                break
        if not ok:
            return None
    try:
        order, mulf, invf = lib.semidirect_group(m, k, r)
    except ValueError:
        return None
    if order != G:
        return None
    table = [[mulf(a, b) for b in range(G)] for a in range(G)]
    inv = [invf(a) for a in range(G)]
    return G, table, inv


def _adj(G, table, S, invS):
    """Adjacency lists of the bi-Cayley graph with connection set S."""
    N = 2 * G
    adj = [None] * N
    for g in range(G):
        row = table[g]
        adj[g] = [G + row[s] for s in S]
    for h in range(G):
        row = table[h]
        adj[G + h] = [row[t] for t in invS]
    return adj


def _reach_count(adj, N, src, D):
    """Number of vertices within distance D of src."""
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
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return cnt


def _bad(G, table, inv, S, D):
    """Number of (source, vertex) pairs at distance > D from sources A_e and B_e. Zero means diameter <= D."""
    invS = [inv[s] for s in S]
    adj = _adj(G, table, S, invS)
    N = 2 * G
    bad = 0
    for src in (0, G):
        bad += N - _reach_count(adj, N, src, D)
    return bad


def _climb(G, table, inv, d, D, rng, deadline, iters):
    """Hill-climb a connection set S of d distinct group elements; returns S with zero cost or None."""
    S = rng.sample(range(G), d)
    c = _bad(G, table, inv, S, D)
    for it in range(iters):
        if c == 0:
            return S
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct = _bad(G, table, inv, T, D)
        if ct <= c or rng.random() < 0.03:
            S, c = T, ct
    return S if c == 0 else None


def _bicayley_edges(G, table, S):
    return [(g, G + table[g][s]) for g in range(G) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Projective plane incidence graph (diameter 3) when a prime power q = d-1 or smaller exists.
    for q in range(min(d - 1, 25), 1, -1):
        if lib.is_prime_power(q):
            n, e = lib.projective_plane_incidence(q)
            consider(n, e)
            break

    # Main search: bi-Cayley graphs over random permutation groups and semidirect products,
    # targeting group orders just above the current best half-order.
    while time.monotonic() < deadline:
        lo = max(d, best_n // 2 + 1)
        hi = lo + 40
        if rng.random() < 0.5:
            grp = _perm_group(lo, hi, rng)
        else:
            grp = _semi_group(rng.randint(lo, hi), rng)
        if grp is None:
            continue
        G, table, inv = grp
        if G < d:
            continue
        S = _climb(G, table, inv, d, D, rng, deadline, iters=1500)
        if S is not None:
            consider(2 * G, _bicayley_edges(G, table, S))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
