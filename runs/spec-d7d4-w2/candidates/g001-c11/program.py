import itertools
import random
import time

import lib


def _is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def _normalize(v, q):
    """Scale v so its first nonzero coordinate is 1 (mod prime q). Returns None for the zero vector."""
    for c in v:
        if c % q:
            inv = pow(c, q - 2, q)
            return tuple((x * inv) % q for x in v)
    return None


def _gq_incidence(q):
    """Point-line incidence of the symplectic generalized quadrangle W(q), q prime.

    Returns (N, lines, pts) where N = number of points = number of lines = (q+1)(q^2+1),
    and lines is a list of sets of point indices.
    """
    raw = {_normalize(v, q) for v in itertools.product(range(q), repeat=4)}
    raw.discard(None)
    pts = sorted(raw)
    idx = {p: i for i, p in enumerate(pts)}

    def form(x, y):
        return (x[0] * y[1] - x[1] * y[0] + x[2] * y[3] - x[3] * y[2]) % q

    lines = set()
    for i, p in enumerate(pts):
        for j in range(i + 1, len(pts)):
            r = pts[j]
            if form(p, r) == 0:
                span = frozenset(
                    idx[_normalize(tuple((a * p[t] + b * r[t]) % q for t in range(4)), q)]
                    for a in range(q) for b in range(q) if (a, b) != (0, 0)
                )
                lines.add(span)
    lines = sorted(lines, key=lambda s: sorted(s))
    return len(pts), [set(s) for s in lines]


def _kuhn(adj, n):
    """Perfect matching in a bipartite graph with left and right sides 0..n-1.

    adj[u] lists right vertices for left vertex u. Returns match_r (match_r[v] = u) or None.
    """
    match_r = [-1] * n

    def augment(u, seen):
        for v in adj[u]:
            if not seen[v]:
                seen[v] = True
                if match_r[v] == -1 or augment(match_r[v], seen):
                    match_r[v] = u
                    return True
        return False

    for u in range(n):
        if not augment(u, [False] * n):
            return None
    return match_r


def _gq_graph(d, rng):
    """Degree-d bipartite graph of diameter 4 from W(q), q the largest prime with q+1 <= d.

    Start from the incidence graph of W(q) (degree q+1, diameter 4). Add k = d-(q+1) extra
    perfect matchings between non-incident point-line pairs. Adding edges between the two
    sides keeps the graph bipartite and can only shrink distances, so diameter stays <= 4.
    """
    primes = [p for p in range(2, d) if _is_prime(p) and p + 1 <= d]
    if not primes:
        return None
    q = max(primes)
    k = d - (q + 1)
    N, lines = _gq_incidence(q)
    if len(lines) != N or N != (q + 1) * (q * q + 1):
        return None

    pairs = [(i, j) for j, line in enumerate(lines) for i in line]
    used = set(pairs)
    for _ in range(k):
        adj = []
        for i in range(N):
            cand = [j for j in range(N) if (i, j) not in used]
            rng.shuffle(cand)
            adj.append(cand)
        match_r = _kuhn(adj, N)
        if match_r is None:
            return None
        for j in range(N):
            i = match_r[j]
            used.add((i, j))
            pairs.append((i, j))

    edges = [(i, N + j) for i, j in pairs]
    return 2 * N, edges


def _haar_search(d, D, rng, deadline):
    """Cyclic Haar-graph search (fallback). Always returns a valid graph for D >= 2."""
    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
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
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if D < 2 or d < 2:
        return 2, [(0, 1)]

    # Calibration case with a known optimal construction.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    best = None

    # Structured candidate: generalized quadrangle based (targets D = 4).
    if D == 4:
        try:
            cand = _gq_graph(d, rng)
            if cand is not None:
                n, edges = cand
                if lib.is_valid(n, edges, d, D):
                    best = (n, edges)
        except Exception:
            best = None

    # Safe fallback / alternative: cyclic Haar search. Keep whichever is larger.
    try:
        alt = _haar_search(d, D, rng, deadline)
        if lib.is_valid(alt[0], alt[1], d, D):
            if best is None or alt[0] > best[0]:
                best = alt
    except Exception:
        pass

    if best is None:
        n, edges = lib.haar_graph(d, range(d))
        best = (n, edges)
    return best
