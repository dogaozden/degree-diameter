import itertools
import random
import time

import lib


# ---------------------------------------------------------------------------
# Generalized quadrangle W(q): points of PG(3,q), lines = totally isotropic
# lines of a symplectic form. Incidence graph has order 2(q+1)(q^2+1),
# degree q+1, diameter 4.
# ---------------------------------------------------------------------------

def _norm(F, v):
    """Scale a nonzero vector so its first nonzero coordinate is 1."""
    for c in v:
        if c:
            s = F.inv(c)
            return tuple(F.mul(s, x) for x in v)
    return None


def _gq_points(F, q):
    """Normalized nonzero vectors of GF(q)^4 (points of PG(3,q))."""
    pts = []
    for v in itertools.product(range(q), repeat=4):
        if any(v) and _norm(F, v) == v:
            pts.append(v)
    return pts


def _gq_incidence(q):
    """Return (m, edges) for the W(q) incidence graph: points 0..m-1, lines m..2m-1."""
    F = lib.GF(q)
    P = _gq_points(F, q)
    m = len(P)
    index = {p: i for i, p in enumerate(P)}

    def form(x, y):
        return F.add(F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0])),
                     F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    combos = [(1, 0)] + [(t, 1) for t in range(q)]
    lines = set()
    for i in range(m):
        p = P[i]
        for j in range(i + 1, m):
            r = P[j]
            if form(p, r):
                continue
            on = set()
            for a, b in combos:
                v = tuple(F.add(F.mul(a, x), F.mul(b, y)) for x, y in zip(p, r))
                on.add(index[_norm(F, v)])
            lines.add(frozenset(on))
    lines = sorted(lines, key=sorted)
    if len(lines) != m or any(len(L) != q + 1 for L in lines):
        raise ValueError("unexpected GQ structure")
    edges = [(i, m + j) for j, L in enumerate(lines) for i in sorted(L)]
    return m, edges


def _add_matching(m, edges, rng):
    """Add a random perfect matching between points and lines that are not already incident.

    Every vertex gains exactly one degree, so the degree goes from q+1 to q+2.
    Adding edges never increases distances, so diameter 4 is preserved.
    """
    adj = set(edges)
    for _ in range(300):
        pts = list(range(m))
        rng.shuffle(pts)
        used = set()
        match = []
        ok = True
        for p in pts:
            cand = [l for l in range(m, 2 * m) if l not in used and (p, l) not in adj]
            if not cand:
                ok = False
                break
            l = rng.choice(cand)
            used.add(l)
            match.append((p, l))
        if ok:
            return edges + match
    return None


def _gq_base(d, rng):
    """Return (n, edges) for a degree-d diameter-4 bipartite base graph, or None."""
    # Option 1: d-1 is a prime power -> W(d-1) directly, degree d.
    # Option 2: d-2 is a prime power -> W(d-2) plus a matching, degree d.
    for q, need_matching in ((d - 1, False), (d - 2, True)):
        if q < 2 or not lib.is_prime_power(q):
            continue
        try:
            m, edges = _gq_incidence(q)
        except (ValueError, AssertionError):
            continue
        if need_matching:
            edges = _add_matching(m, edges, rng)
            if edges is None:
                continue
        return 2 * m, edges
    return None


# ---------------------------------------------------------------------------
# New move: pair insertion by edge rewiring, plus neutral 2-switches.
#
# Insertion: pick 6 edges (a_i, b_i) with distinct a's and distinct b's.
# Remove them, add new vertices x (A-side) and y (B-side) with edges
# x-b_i, a_i-y for all i, and x-y. Every old vertex keeps its degree,
# x and y reach degree 7, and bipartiteness is kept. Each accepted move
# adds 2 vertices.
#
# 2-switch: swap endpoints of two edges to diversify the graph, accepted
# only if the diameter bound still holds.
# ---------------------------------------------------------------------------

def _grow(n, edges, d, D, rng, deadline):
    """Randomized search that only keeps graphs satisfying the diameter bound."""
    E = list(edges)
    eset = set(E)
    best = (n, list(E))
    cur_n = n
    while time.monotonic() < deadline:
        if rng.random() < 0.5:
            if len(E) < 6:
                break
            idx = rng.sample(range(len(E)), 6)
            As = [E[i][0] for i in idx]
            Bs = [E[i][1] for i in idx]
            if len(set(As)) < 6 or len(set(Bs)) < 6:
                continue
            x, y = cur_n, cur_n + 1
            drop = set(idx)
            newE = [E[i] for i in range(len(E)) if i not in drop]
            newE += [(x, b) for b in Bs]
            newE += [(a, y) for a in As]
            newE.append((x, y))
            if lib.within_diameter(cur_n + 2, newE, D):
                E = newE
                eset = set(E)
                cur_n += 2
                if cur_n > best[0]:
                    best = (cur_n, list(E))
        else:
            if len(E) < 2:
                break
            i, j = rng.sample(range(len(E)), 2)
            a1, b1 = E[i]
            a2, b2 = E[j]
            if a1 == a2 or b1 == b2:
                continue
            e1, e2 = (a1, b2), (a2, b1)
            if e1 in eset or e2 in eset:
                continue
            newE = list(E)
            newE[i] = e1
            newE[j] = e2
            if lib.within_diameter(cur_n, newE, D):
                E = newE
                eset = set(E)
    return best


# ---------------------------------------------------------------------------
# Fallback: cyclic Haar-graph search (the parent's method).
# ---------------------------------------------------------------------------

def _haar_search(d, D, rng, deadline):
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    if D == 4:
        base = _gq_base(d, rng)
        if base is not None and lib.is_valid(base[0], base[1], d, D):
            n, edges = _grow(base[0], base[1], d, D, rng, deadline)
            if lib.is_valid(n, edges, d, D):
                return n, edges
            return base

    return _haar_search(d, D, rng, deadline)
