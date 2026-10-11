import itertools
import random
import time

import lib


def _largest_prime_power_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_points_lines(q):
    """Points of PG(3,q) and totally isotropic lines of the symplectic form (W(q))."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [F.neg(a) for a in range(q)]
    inv = [F.inv(a) if a else 0 for a in range(q)]

    def form(x, y):
        s = add[mul[x[0]][y[1]]][neg[mul[x[1]][y[0]]]]
        s = add[s][mul[x[2]][y[3]]]
        return add[s][neg[mul[x[3]][y[2]]]]

    def normalize(v):
        c = next(c for c in v if c)
        k = inv[c]
        return tuple(mul[k][x] for x in v)

    lines = set()
    for i in range(P):
        p = pts[i]
        for j in range(i + 1, P):
            r = pts[j]
            if form(p, r):
                continue
            members = {i, j}
            for c in range(1, q):
                v = tuple(add[p[k]][mul[c][r[k]]] for k in range(4))
                members.add(index[normalize(v)])
            lines.add(tuple(sorted(members)))
    return P, sorted(lines)


def _gq_graph(q):
    """Incidence graph of W(q) (a generalized quadrangle GQ(q,q)).

    Returns (n, edges, P, L, cover) where cover[l] is a bitmask of the lines
    equal to or concurrent with line l. Diameter of this graph is 4.
    """
    P, lines = _gq_points_lines(q)
    L = len(lines)
    if L != (q + 1) * (q * q + 1) or P != (q + 1) * (q * q + 1):
        raise ValueError("unexpected GQ size")
    n = P + L
    edges = []
    through = [0] * P
    for li, mem in enumerate(lines):
        for x in mem:
            edges.append((x, P + li))
            through[x] |= 1 << li
    cover = []
    for mem in lines:
        m = 0
        for x in mem:
            m |= through[x]
        cover.append(m)
    return n, edges, P, L, cover


def _extend_with_points(d, q, n, edges, P, L, cover, deadline, rng):
    """Greedily add new point-side vertices.

    A new point adjacent to a set A of lines keeps diameter 4 exactly when A
    dominates all lines (every line is in A or concurrent with a member of A):
    then distances to all points, to all lines and to other new points stay <= 4.
    Each line can absorb d - (q+1) extra new neighbours.
    """
    cap = d - (q + 1)
    if cap <= 0:
        return n, edges
    full = (1 << L) - 1
    used = [0] * L
    extra = []
    npts = 0
    while time.monotonic() < deadline:
        pool = [l for l in range(L) if used[l] < cap]
        rng.shuffle(pool)
        U = full
        chosen = []
        while U and len(chosen) < d:
            best, bc = -1, 0
            for l in pool:
                c = (cover[l] & U).bit_count()
                if c > bc:
                    best, bc = l, c
            if bc == 0:
                break
            chosen.append(best)
            U &= ~cover[best]
        if U:
            continue
        v = n + npts
        npts += 1
        for l in chosen:
            used[l] += 1
            extra.append((v, P + l))
    return n + npts, edges + extra


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    if D == 4:
        q = _largest_prime_power_at_most(d - 1)
        if q is not None and q >= 2:
            try:
                n, edges, P, L, cover = _gq_graph(q)
                if lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    n2, e2 = _extend_with_points(d, q, n, edges, P, L, cover,
                                                 deadline, rng)
                    if n2 > n and lib.is_valid(n2, e2, d, D):
                        return n2, e2
                    return best
            except Exception:
                pass

    # Fallback: Haar graphs over Z_m (parent approach).
    best = lib.haar_graph(d, range(d))
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best
