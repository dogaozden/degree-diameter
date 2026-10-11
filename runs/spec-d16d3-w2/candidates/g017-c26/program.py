"""Bipartite diameter-D graph builder with two families for D = 3.

Family 1: PG(2, q) incidence graph (q the largest prime power with q + 1 <= d),
plus extra A/B vertices from independent point and line packings that use the
spare degree s = d - q - 1. Those packings are the same as the parent's arc
extension, but they are chosen independently, so the point set S and the line
set T can differ. Diameter 3 is preserved.

Family 2 (new in this version): Haar graphs H(m, S) of Z_m with |S| = d. A
Haar graph has diameter <= 3 exactly when S - S covers Z_m (for vertex pairs on
the same side) and S - S + S covers Z_m (for pairs on opposite sides). The
search hill-climbs S to make both covers complete, for increasing m, so it
targets orders above the current best.

Every candidate is checked with lib.is_valid before it is kept. K_{d,d} is the
fallback. The projective-plane family is kept because it already gives valid
graphs quickly.
"""
import random
import time

import lib


# ----------------------------------------------------------------------------
# Family 1: PG(2, q) with independent point and line packings.
# ----------------------------------------------------------------------------

def _pg_lists(q, edges, m):
    pl = [[] for _ in range(m)]  # point -> lines
    lp = [[] for _ in range(m)]  # line -> points
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return pl, lp


def _pack(m, cons, cover, s, rng, deadline):
    """Large set X of items 0..m-1 with every constraint used by <= s members of X.

    cons[i]: constraints used by item i. cover[j]: items that use constraint j.
    Random insert, with single-blocker swaps and occasional perturbation.
    """
    inX = [False] * m
    load = [0] * m
    X = []
    best = []

    def add(i):
        inX[i] = True
        X.append(i)
        for j in cons[i]:
            load[j] += 1

    def remove(i):
        inX[i] = False
        X.remove(i)
        for j in cons[i]:
            load[j] -= 1

    def blockers(i):
        out = set()
        for j in cons[i]:
            if load[j] >= s:
                for k in cover[j]:
                    if inX[k]:
                        out.add(k)
        return out

    it = 0
    while True:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(m)
        if inX[i]:
            continue
        B = blockers(i)
        if not B:
            add(i)
        elif len(B) == 1 or (len(B) <= 2 and rng.random() < 0.05):
            for k in list(B):
                remove(k)
            add(i)
        else:
            continue
        if X and rng.random() < 0.002:
            remove(rng.choice(X))
        if len(X) > len(best):
            best = list(X)
    return best


def _pg_extension(q, edges, m, S, T):
    """PG incidence plus an A-vertex per point in S and a B-vertex per line in T."""
    pts_base = 0
    line_base = m
    a_base = 2 * m
    b_base = 2 * m + len(S)
    n = 2 * m + len(S) + len(T)
    E = list(edges)
    pl, lp = _pg_lists(q, edges, m)
    for t, P in enumerate(S):
        for L in pl[P]:
            E.append((a_base + t, line_base + L))
    for t, L in enumerate(T):
        for P in lp[L]:
            E.append((pts_base + P, b_base + t))
    side = [0] * m + [1] * m + [0] * len(S) + [1] * len(T)
    return n, E, side


def _saturate(n, E, side, d, rng):
    """Add edges between opposite sides while both endpoints have spare degree.

    This only shortens distances, so diameter stays <= 3. Degree is checked by is_valid.
    """
    deg = [0] * n
    ex = set()
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
        ex.add((min(u, v), max(u, v)))
    left = [v for v in range(n) if side[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if side[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in ex]
    rng.shuffle(pairs)
    out = list(E)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            out.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return out


# ----------------------------------------------------------------------------
# Family 2: Haar graphs of Z_m with a hill-climbed connection set S (|S| = d).
# ----------------------------------------------------------------------------

def _haar_cost(S, m):
    """Uncovered residues for the diameter-3 conditions of H(m, S).

    Same-side pairs need S - S to cover all nonzero residues.
    Opposite-side pairs need S - S + S to cover all residues.
    """
    diffs = {(a - b) % m for a in S for b in S}
    sums = {(x + s) % m for x in diffs for s in S}
    return (m - len(diffs)) + (m - len(sums))


def _haar_climb(m, d, rng, deadline):
    """Random-restart-free hill climb on S (contains 0). Returns S with cost 0, or None."""
    S = [0] + rng.sample(range(1, m), d - 1)
    c = _haar_cost(S, m)
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct = _haar_cost(T, m)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Family 1: PG(2, q) plus independent point and line packings.
        q = next((x for x in range(d - 1, 1, -1) if lib.is_prime_power(x)), None)
        if q is not None:
            n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)
            s = d - q - 1
            if s >= 1:
                m = n0 // 2
                pl, lp = _pg_lists(q, e0, m)
                now = time.monotonic()
                S = _pack(m, pl, lp, s, rng, now + 0.25 * (deadline - now))
                now = time.monotonic()
                T = _pack(m, lp, pl, s, rng, now + 0.5 * (deadline - now))
                if S or T:
                    n1, e1, side = _pg_extension(q, e0, m, S, T)
                    consider(n1, e1)
                    e2 = _saturate(n1, e1, side, d, rng)
                    consider(n1, e2)

        # Family 2: Haar graph search for orders above the current best.
        if d >= 2:
            m_cap = moore // 2
            m = max(d + 1, best_n // 2 + 1)
            fails = 0
            while time.monotonic() < deadline:
                m = min(m, m_cap)
                S = _haar_climb(m, d, rng, min(deadline, time.monotonic() + 3.0))
                if S is not None:
                    n, e = lib.haar_graph(m, S)
                    consider(n, e)
                    m += 1
                    fails = 0
                else:
                    fails += 1
                    if fails >= 2:
                        m = max(d + 1, m - 1)
                        fails = 0

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
