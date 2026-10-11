import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base families (safe fallbacks).
# ----------------------------------------------------------------------------

def _conic_set(q):
    """Point indices of a conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_candidates(d):
    """Candidate (n, edges, colour) graphs: PG(2,q) incidence and its arc extension.

    For the arc extension, each point P in S gets a new colour-0 vertex joined to the
    q+1 lines through P, and each line j in S gets a new colour-1 vertex joined to the
    q+1 points on it. Every line and point then gains at most 2 extra edges, so this
    is valid for d >= q + 3.
    """
    out = []
    qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
    for q in qs:
        s = d - q - 1
        n2, E = lib.projective_plane_incidence(q)
        m = n2 // 2
        nb = [[] for _ in range(n2)]
        for u, v in E:
            nb[u].append(v)
            nb[v].append(u)
        color0 = [0] * m + [1] * m
        out.append((n2, list(E), color0))
        if s >= 2:
            S = _conic_set(q)
            k = len(S)
            E2 = list(E)
            for t, P in enumerate(S):
                for L in nb[P]:
                    E2.append((2 * m + t, L))
            for t, j in enumerate(S):
                for Q in nb[m + j]:
                    E2.append((Q, 2 * m + k + t))
            out.append((2 * m + 2 * k, E2, color0 + [0] * k + [1] * k))
    return out


# ----------------------------------------------------------------------------
# Repair search: grow by two vertices (one per side), then anneal the edges
# until every pair is within distance 3. Degree-preserving 2-switches and
# endpoint transfers keep max degree <= d; bipartiteness is kept by colours.
# ----------------------------------------------------------------------------

def _cost(n, nbrs, D):
    """Number of unordered vertex pairs at distance more than D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in nbrs[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _accept(delta, T, rng):
    return delta <= 0 or rng.random() < math.exp(-delta / T)


def _try_grow(n, color, E, d, deadline, rng):
    """Add one vertex per side and search for diameter 3. Returns (N, colour, edges) or None."""
    N = n + 2
    col = list(color) + [0, 1]
    nbrs = [set() for _ in range(N)]
    elist = []
    for u, v in E:
        p, q = (u, v) if col[u] == 0 else (v, u)
        if q not in nbrs[p]:
            nbrs[p].add(q)
            nbrs[q].add(p)
            elist.append((p, q))

    zeros = [v for v in range(N) if col[v] == 0]
    ones = [v for v in range(N) if col[v] == 1]

    # Saturate spare degree (only adds edges, so distances never grow).
    pairs = [(x, y) for x in zeros for y in ones]
    rng.shuffle(pairs)
    for x, y in pairs:
        if len(nbrs[x]) < d and len(nbrs[y]) < d and y not in nbrs[x]:
            nbrs[x].add(y)
            nbrs[y].add(x)
            elist.append((x, y))

    cost = _cost(N, nbrs, 3)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = 0.03 ** ((now - t0) / span)  # geometric cooling from 1.0 to 0.03
        if rng.random() < 0.7 and len(elist) >= 2:
            i = rng.randrange(len(elist))
            j = rng.randrange(len(elist))
            if i == j:
                continue
            p1, q1 = elist[i]
            p2, q2 = elist[j]
            if p1 == p2 or q1 == q2 or q2 in nbrs[p1] or q1 in nbrs[p2]:
                continue
            nbrs[p1].discard(q1); nbrs[q1].discard(p1)
            nbrs[p2].discard(q2); nbrs[q2].discard(p2)
            nbrs[p1].add(q2); nbrs[q2].add(p1)
            nbrs[p2].add(q1); nbrs[q1].add(p2)
            c2 = _cost(N, nbrs, 3)
            if _accept(c2 - cost, T, rng):
                cost = c2
                elist[i] = (p1, q2)
                elist[j] = (p2, q1)
            else:
                nbrs[p1].discard(q2); nbrs[q2].discard(p1)
                nbrs[p2].discard(q1); nbrs[q1].discard(p2)
                nbrs[p1].add(q1); nbrs[q1].add(p1)
                nbrs[p2].add(q2); nbrs[q2].add(p2)
        else:
            if not elist:
                continue
            i = rng.randrange(len(elist))
            p, q = elist[i]
            if rng.random() < 0.5:
                # Move the colour-1 endpoint q to a deficient colour-1 vertex y.
                cands = [y for y in ones if len(nbrs[y]) < d and y not in nbrs[p]]
                if not cands:
                    continue
                y = rng.choice(cands)
                nbrs[p].discard(q); nbrs[q].discard(p)
                nbrs[p].add(y); nbrs[y].add(p)
                c2 = _cost(N, nbrs, 3)
                if _accept(c2 - cost, T, rng):
                    cost = c2
                    elist[i] = (p, y)
                else:
                    nbrs[p].discard(y); nbrs[y].discard(p)
                    nbrs[p].add(q); nbrs[q].add(p)
            else:
                # Move the colour-0 endpoint p to a deficient colour-0 vertex x.
                cands = [x for x in zeros if len(nbrs[x]) < d and x not in nbrs[q]]
                if not cands:
                    continue
                x = rng.choice(cands)
                nbrs[p].discard(q); nbrs[q].discard(p)
                nbrs[x].add(q); nbrs[q].add(x)
                c2 = _cost(N, nbrs, 3)
                if _accept(c2 - cost, T, rng):
                    cost = c2
                    elist[i] = (x, q)
                else:
                    nbrs[x].discard(q); nbrs[q].discard(x)
                    nbrs[p].add(q); nbrs[q].add(p)
    return N, col, elist


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback
    cur_n, cur_e = fallback
    cur_col = [0] * d + [1] * d

    if D >= 3:
        # Largest valid arc-extended PG(2,q) candidate (the record-level base).
        for n, E, col in _arc_candidates(d):
            if n > best_n and lib.is_valid(n, E, d, D):
                best_n, best_e = n, E
                cur_n, cur_e, cur_col = n, E, col

    # Repair-growth gamble for the target diameter-3 case.
    if D == 3:
        moore = lib.moore_bound(d, D)
        slice_len = max(2.0, (deadline - time.monotonic()) / 4.0)
        while time.monotonic() < deadline and cur_n < moore:
            end = min(deadline, time.monotonic() + slice_len)
            res = _try_grow(cur_n, cur_col, cur_e, d, end, rng)
            if res is None:
                continue
            n2, col2, e2 = res
            if not lib.is_valid(n2, e2, d, D):
                continue
            cur_n, cur_col, cur_e = n2, col2, e2
            if n2 > best_n:
                best_n, best_e = n2, e2

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, best_e
