import random
import time

import lib


def _parent(d, D, seed, deadline):
    """Original search: Haar graphs found by random connection sets (safe fallback)."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    rng = random.Random(seed)
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


def _norm(F, v):
    """Scale a projective vector so its first nonzero coordinate is 1."""
    c = next(x for x in v if x)
    inv = F.inv(c)
    return tuple(F.mul(inv, x) for x in v)


def _conic_twin_base(q):
    """PG(2,q) incidence plus twins of an oval's points and of its tangent lines.

    Point-twins x_P (A side) join the lines through P; line-twins y_L (B side) join
    the points on L. Each line gains one A-neighbour per oval point on it (<= 2),
    each point gains one B-neighbour per tangent through it (<= 2), so with q = d-3
    the max degree is q+3 = d. Twins keep diameter 3 (distances to twins equal
    distances to originals, and the twin pairs are checked by the final is_valid).
    Order: 2(q^2+q+1) + 2(q+1) = 2(q^2+2q+2); for q = 13 this is 394.
    """
    F = lib.GF(q)
    pts = lib.projective_points(q)
    m = len(pts)
    index = {p: i for i, p in enumerate(pts)}
    _, base = lib.projective_plane_incidence(q)  # points 0..m-1, lines m..2m-1
    pt_lines = [[] for _ in range(m)]
    line_pts = [[] for _ in range(m)]
    for u, v in base:
        pt_lines[u].append(v - m)
        line_pts[v - m].append(u)

    # Conic (1, t, t^2) and (0, 0, 1); its tangent lines in coordinates a x + b y + c z = 0.
    conic = [index[_norm(F, (1, t, F.mul(t, t)))] for t in range(q)]
    conic.append(index[_norm(F, (0, 0, 1))])
    tangents = [index[_norm(F, (F.neg(F.mul(t, t)), F.add(t, t), F.neg(1)))] for t in range(q)]
    tangents.append(index[_norm(F, (1, 0, 0))])

    n = 2 * m
    edges = list(base)
    side = [0] * m + [1] * m
    for P in conic:
        x = n
        n += 1
        side.append(0)
        edges.extend((x, m + j) for j in pt_lines[P])
    for j in tangents:
        y = n
        n += 1
        side.append(1)
        edges.extend((i, y) for i in line_pts[j])
    return n, edges, side


def _cover(universe, cand, adj, d, rng):
    """Greedy cover: choose <= d candidates whose neighbourhoods cover `universe`."""
    uncovered = set(universe)
    rng.shuffle(cand)
    chosen = []
    while uncovered:
        if len(chosen) >= d or not cand:
            return None
        best, gain = None, 0
        for c in cand:
            g = len(uncovered & adj[c])
            if g > gain:
                best, gain = c, g
        if best is None:
            return None
        chosen.append(best)
        uncovered -= adj[best]
        cand.remove(best)
    return chosen


def _extend(n, edges, side, d, D, deadline, rng):
    """Add free A-B edges, then try random greedy-cover new vertices; keep only valid growth."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    edges = list(edges)
    side = list(side)

    # Extra A-B edges never increase distances and keep bipartiteness.
    A = [v for v in range(n) if side[v] == 0]
    B = [v for v in range(n) if side[v] == 1]
    rng.shuffle(A)
    rng.shuffle(B)
    for a in A:
        for b in B:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)
                edges.append((a, b))

    want = 0
    while time.monotonic() < deadline:
        s = want
        want ^= 1
        universe = [v for v in range(n) if side[v] == s]
        cand = [c for c in range(n) if side[c] == 1 - s and len(adj[c]) < d]
        chosen = _cover(universe, cand, adj, d, rng)
        if chosen is None:
            continue
        z = n
        new_edges = [(c, z) for c in chosen]
        n2 = n + 1
        side2 = side + [s]
        edges2 = edges + new_edges
        if lib.is_valid(n2, edges2, d, D):
            n = n2
            side = side2
            edges = edges2
            adj.append(set(chosen))
            for c in chosen:
                adj[c].add(z)
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    q = d - 3
    if (D == 3 and not lib.is_prime_power(d - 1) and q >= 3 and q % 2 == 1
            and lib.is_prime_power(q)):
        try:
            n, edges, side = _conic_twin_base(q)
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
                try:
                    rng = random.Random(seed)
                    n2, e2 = _extend(n, edges, side, d, D, deadline, rng)
                    if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                        best = (n2, e2)
                except Exception:
                    pass
                return best
        except Exception:
            pass
    return _parent(d, D, seed, deadline)
