import random
import time
import lib


def _conic_graph(q):
    """Incidence graph of PG(2,q) (q odd) plus two new vertex classes.

    Points and lines of PG(2,q) give 2m vertices, each of degree q+1. A conic C
    (q+1 points, no three collinear) gives new point-side vertices x_P, one per
    conic point P, joined to the q+1 lines through P. The tangents of C (q+1 lines,
    each point on at most 2) give new line-side vertices y_L, joined to the q+1
    points on L. Every old line gets at most 2 extra edges and every old point
    at most 2, so max degree is q+3. Distances stay <= 3 by the usual
    projective-plane argument. Order is 2(q^2+2q+2), which is 394 for q=13.
    """
    F = lib.GF(q)
    pts = lib.projective_points(q)
    m = len(pts)
    pidx = {v: i for i, v in enumerate(pts)}
    two = F.add(1, 1)

    def norm(v):
        c = next(x for x in v if x)
        ci = F.inv(c)
        return tuple(F.mul(x, ci) for x in v)

    def dot(a, b):
        s = 0
        for x, y in zip(a, b):
            s = F.add(s, F.mul(x, y))
        return s

    conic = [norm((1, t, F.mul(t, t))) for t in range(q)] + [(0, 0, 1)]
    tang = [norm((F.mul(t, t), F.neg(F.mul(two, t)), 1)) for t in range(q)] + [(1, 0, 0)]
    if any(c not in pidx for c in conic + tang):
        return None
    if len(set(conic)) != q + 1 or len(set(tang)) != q + 1:
        return None
    # Arc property: no line meets the conic in 3+ points.
    for L in pts:
        if sum(1 for P in conic if dot(P, L) == 0) > 2:
            return None
    # Dual arc property: no point lies on 3+ tangent lines.
    for P in pts:
        if sum(1 for L in tang if dot(P, L) == 0) > 2:
            return None

    n = 2 * m + 2 * (q + 1)
    edges = []
    for i, P in enumerate(pts):
        for j, L in enumerate(pts):
            if dot(P, L) == 0:
                edges.append((i, m + j))
    base = 2 * m
    for k, P in enumerate(conic):
        x = base + k
        for j, L in enumerate(pts):
            if dot(P, L) == 0:
                edges.append((x, m + j))
    base2 = base + len(conic)
    for k, L in enumerate(tang):
        y = base2 + k
        for i, P in enumerate(pts):
            if dot(P, L) == 0:
                edges.append((i, y))
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    if D == 3:
        # Largest odd prime power q with q+3 <= d, so each old vertex keeps spare degree.
        for qc in range(d - 3, 2, -1):
            if qc % 2 == 1 and lib.is_prime_power(qc):
                try:
                    res = _conic_graph(qc)
                except Exception:
                    res = None
                if res is not None and lib.is_valid(res[0], res[1], d, D):
                    return res
                break
    # Fallback: random Haar-graph search (valid by construction, checked by diameter).
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # complete bipartite K_{d,d}: always valid
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
