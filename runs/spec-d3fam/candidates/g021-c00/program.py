import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe base constructions (diameter 3 or less).
# ----------------------------------------------------------------------------

def _ara(d):
    """Araujo-Pardo & Lopez graph for d = q + 2, q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: Haar-type bipartite graphs over finite abelian groups.
#
# For an abelian group Gamma of order G and a set S of size d, let A_g be joined
# to B_h iff h - g is in S. The graph is bipartite and d-regular on 2G vertices.
# Distances: (A_0, A_x) is 2 steps iff x is in S - S, and (A_0, B_y) is 1 or 3
# steps for y in S or S - S + S. So if S - S covers all of Gamma, the diameter
# is at most 3. This is a difference-covering problem, and it is independent of
# the voltage-lift search used by the parent.
# ----------------------------------------------------------------------------

_SUB_CACHE = {}


def _sub_table(a, b):
    """Subtraction table of Z_a x Z_b with element x*b + y; sub[x][y] = x - y."""
    key = (a, b)
    if key in _SUB_CACHE:
        return _SUB_CACHE[key]
    G = a * b
    coords = [divmod(x, b) for x in range(G)]
    sub = []
    for x1, y1 in coords:
        sub.append([((x1 - x2) % a) * b + ((y1 - y2) % b) for x2, y2 in coords])
    _SUB_CACHE[key] = sub
    return sub


def _random_factor(G, rng):
    """Random factorisation G = a * b, giving the group Z_a x Z_b."""
    divs = [a for a in range(1, G + 1) if G % a == 0]
    a = rng.choice(divs)
    return a, G // a


def _haar_edges(G, a, b, S):
    """Edges of the bi-Cayley graph: A_g (index g) joined to B_{g+s} (index G + g + s)."""
    E = []
    for g in range(G):
        x1, y1 = divmod(g, b)
        for s in S:
            x2, y2 = divmod(s, b)
            h = ((x1 + x2) % a) * b + (y1 + y2) % b
            E.append((g, G + h))
    return E


def _anneal(G, sub, d, rng, deadline, iters):
    """Find S (|S| = d, containing 0) with S - S covering all nonzero group elements.

    Minimises the number of uncovered nonzero elements by single-element swaps.
    Returns S, or None if no cover is found within the budget.
    """
    S = [0] + rng.sample(range(1, G), d - 1)
    inS = set(S)
    cnt = [0] * G          # cnt[x] = number of ordered pairs (p, q), p != q, with p - q = x
    cnt[0] = d             # the diagonal; never changed
    for p in S:
        row = sub[p]
        for q in S:
            if p != q:
                cnt[row[q]] += 1
    unc = sum(1 for x in range(1, G) if cnt[x] == 0)

    for it in range(iters):
        if unc == 0:
            break
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        a = S[i]
        y = rng.randrange(G)
        if y in inS:
            continue
        others = [S[j] for j in range(d) if j != i]
        sa = sub[a]
        sy = sub[y]
        old = unc

        # Remove the differences of a.
        for b in others:
            for x in (sa[b], sub[b][a]):
                cnt[x] -= 1
                if cnt[x] == 0:
                    unc += 1
        # Add the differences of y.
        for b in others:
            for x in (sy[b], sub[b][y]):
                if cnt[x] == 0:
                    unc -= 1
                cnt[x] += 1

        delta = unc - old
        T = 0.5 * (1.0 - it / iters) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            inS.discard(a)
            inS.add(y)
        else:
            # Undo: remove y's differences, restore a's.
            for b in others:
                for x in (sy[b], sub[b][y]):
                    cnt[x] -= 1
                    if cnt[x] == 0:
                        unc += 1
            for b in others:
                for x in (sa[b], sub[b][a]):
                    if cnt[x] == 0:
                        unc -= 1
                    cnt[x] += 1

    return S if unc == 0 else None


def _diff_search(d, G, deadline, rng, consider):
    """Look for difference covers of order G, G+1, ...; each success gives a Haar graph on 2G vertices."""
    cap = d * (d - 1) + 1          # ordered differences bound: |S - S| <= d(d-1) + 1
    while G <= cap and time.monotonic() < deadline:
        found = None
        while found is None and time.monotonic() < deadline:
            a, b = _random_factor(G, rng)
            sub = _sub_table(a, b)
            S = _anneal(G, sub, d, rng, deadline, 30000)
            if S is not None:
                found = (a, b, S)
        if found is None:
            break
        a, b, S = found
        consider(2 * G, _haar_edges(G, a, b, S))
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
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Record-level and projective-plane constructions first.
        ara = _ara(d)
        if ara is not None:
            consider(ara[0], ara[1])
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Bold new family: difference covers over abelian groups.
        # Start just above the current best (order 2G > best_n).
        _diff_search(d, best_n // 2 + 1, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
