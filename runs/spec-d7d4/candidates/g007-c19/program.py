import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4.
    Points are 0..P-1, lines are P..2P-1."""
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


def _gq_base(d):
    """Largest W(q) with q + 1 <= d and q <= 9 (q a prime power)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return q, _gq_w(q)
    return None


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Graph state helpers. nbr is a list of neighbour sets; A and B are the sides.
# ----------------------------------------------------------------------------

def _sides(n, nbr):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in nbr[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    A = [v for v in range(n) if color[v] != 1]
    B = [v for v in range(n) if color[v] == 1]
    return A, B


def _add(nbr, a, b):
    nbr[a].add(b)
    nbr[b].add(a)


def _rem(nbr, a, b):
    nbr[a].discard(b)
    nbr[b].discard(a)


def _fill(nbr, A, B, d, rng):
    """Greedily add cross edges between spare-capacity vertices (never hurts distances)."""
    sa = [a for a in A if len(nbr[a]) < d]
    sb = [b for b in B if len(nbr[b]) < d]
    rng.shuffle(sa)
    rng.shuffle(sb)
    for a in sa:
        for b in sb:
            if len(nbr[a]) >= d:
                break
            if len(nbr[b]) < d and b not in nbr[a]:
                _add(nbr, a, b)


def _cost(n, nbr, D):
    """Number of unordered pairs at distance greater than D (or unreachable)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in nbr[v]:
                x |= ball[u]
            new.append(x)
        if new == ball:
            break
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


# ----------------------------------------------------------------------------
# Simulated annealing over degree-preserving rewirings, with growth.
# Objective: number of bad pairs. Whenever the objective hits 0, the graph is
# validated and recorded, and two new vertices (one per side) are added.
# ----------------------------------------------------------------------------

def _search(nbr, A, B, d, D, rng, deadline, consider):
    cost = _cost(len(nbr), nbr, D)
    it = 0
    T_HI, T_LO, PERIOD = 3.0, 0.05, 5000

    def snapshot():
        n = len(nbr)
        edges = [(a, b) for a in range(n) for b in nbr[a] if a < b]
        consider(n, edges)

    while time.monotonic() < deadline:
        it += 1
        if cost == 0:
            snapshot()
            a_new = len(nbr)
            nbr.append(set())
            b_new = len(nbr)
            nbr.append(set())
            A.append(a_new)
            B.append(b_new)
            _fill(nbr, A, B, d, rng)
            cost = _cost(len(nbr), nbr, D)
            continue

        phase = (it % PERIOD) / PERIOD
        T = T_HI * (T_LO / T_HI) ** phase

        # Free addition between two spare vertices never increases cost.
        sa = [a for a in A if len(nbr[a]) < d]
        sb = [b for b in B if len(nbr[b]) < d]
        if sa and sb:
            a = rng.choice(sa)
            b = rng.choice(sb)
            if b not in nbr[a]:
                _add(nbr, a, b)
                cost = _cost(len(nbr), nbr, D)
                continue

        E = [(a, b) for a in A for b in nbr[a]]
        if not E:
            continue

        if rng.random() < 0.5:
            # Double-edge swap: keeps every degree.
            if len(E) < 2:
                continue
            a1, b1 = rng.choice(E)
            a2, b2 = rng.choice(E)
            if a1 == a2 or b1 == b2 or b2 in nbr[a1] or b1 in nbr[a2]:
                continue
            _rem(nbr, a1, b1)
            _rem(nbr, a2, b2)
            _add(nbr, a1, b2)
            _add(nbr, a2, b1)
            c2 = _cost(len(nbr), nbr, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                _rem(nbr, a1, b2)
                _rem(nbr, a2, b1)
                _add(nbr, a1, b1)
                _add(nbr, a2, b2)
        else:
            # Relocate one endpoint of an edge onto a spare vertex.
            a, b = rng.choice(E)
            if rng.random() < 0.5:
                cands = [x for x in sb if x != b and x not in nbr[a]]
                if not cands:
                    continue
                nb = rng.choice(cands)
                _rem(nbr, a, b)
                _add(nbr, a, nb)
                c2 = _cost(len(nbr), nbr, D)
                if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                    cost = c2
                else:
                    _rem(nbr, a, nb)
                    _add(nbr, a, b)
            else:
                cands = [x for x in sa if x != a and x not in nbr[b]]
                if not cands:
                    continue
                na = rng.choice(cands)
                _rem(nbr, a, b)
                _add(nbr, na, b)
                c2 = _cost(len(nbr), nbr, D)
                if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                    cost = c2
                else:
                    _rem(nbr, na, b)
                    _add(nbr, a, b)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = {"n": 1, "e": []}

    def consider(n, e):
        if n > best["n"] and lib.is_valid(n, e, d, D):
            best["n"] = n
            best["e"] = e

    try:
        if d == 2:
            m = 2 * D
            consider(m, [(i, (i + 1) % m) for i in range(m)])
        # K_{d,d}: valid for every D >= 2 and optimal for D = 2.
        consider(*lib.haar_graph(d, range(d)))
        if D == 2:
            return best["n"], best["e"]

        if D == 3:
            pg = _pg_best(d)
            if pg is not None:
                consider(pg[0], pg[1])
            return best["n"], best["e"]

        # D >= 4: start from a generalized quadrangle, then anneal and grow.
        base = _gq_base(d)
        if base is None:
            return best["n"], best["e"]
        _, (n0, e0) = base
        nbr = [set() for _ in range(n0)]
        for u, v in e0:
            _add(nbr, u, v)
        A, B = _sides(n0, nbr)
        _fill(nbr, A, B, d, rng)
        n1 = len(nbr)
        consider(n1, [(a, b) for a in range(n1) for b in nbr[a] if a < b])

        _search(nbr, A, B, d, D, rng, deadline, consider)
    except Exception:
        pass
    return best["n"], best["e"]
