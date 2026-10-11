import lib


def _largest_pg_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _arc(q):
    """Point indices of a maximal arc in PG(2, q): at most 2 points on any line.

    q odd: conic (q + 1 points). q even: conic plus nucleus (q + 2 points, a hyperoval).
    """
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _pg_arc_graph(q, S):
    """PG(2, q) incidence plus one new point-side vertex per S-point and one new
    line-side vertex per S-line (lines use the same index set as points).

    Point-side new vertex x_P joins all lines through P. Line-side new vertex y_L
    joins all points on L. Each line gains at most 2 extra edges and each point
    at most 2, because S is an arc. Diameter stays 3.
    """
    n2, base = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in base:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    edges = list(base)
    k = len(S)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            edges.append((x, m + L))
    for t, L in enumerate(S):
        y = 2 * m + k + t
        for Q in line_points[L]:
            edges.append((Q, y))
    return 2 * m + 2 * k, edges


def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D.
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc
        return best

    if D >= 3:
        q = _largest_pg_q(d)
        if q is not None:
            # Plain projective plane incidence graph (diameter 3).
            n0, e0 = lib.projective_plane_incidence(q)
            if n0 > best[0] and lib.is_valid(n0, e0, d, D):
                best = (n0, e0)
            # Arc extension when spare degree s = d - q - 1 is at least 2.
            s = d - q - 1
            if s >= 2:
                try:
                    S = _arc(q)
                    n1, e1 = _pg_arc_graph(q, S)
                    if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                        best = (n1, e1)
                except Exception:
                    pass

    return best
