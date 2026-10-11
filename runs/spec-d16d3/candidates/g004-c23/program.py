"""Diameter-3 bipartite construction: projective plane plus conic arc gadget.

Construction for D >= 3: take the incidence graph of PG(2, q) for the largest prime
powers q with q + 1 <= d. Pick an arc S (no three collinear points) and add one new
point-side vertex A_P and one new line-side vertex B_P per P in S. A_P joins the q+1
lines through P, and B_P joins the q+1 points on line P. Each line then gains
|S ∩ line| <= 2 extra edges, so with d = q + 3 all degrees stay within d and the
diameter stays 3. For d = 16 (q = 13) this uses a conic (14 points), giving 2(183 + 14) = 394.

Honest status: I tried a removal-augmented variant, where deleting some incidences
would free capacity for a larger S. It is ruled out. A_P reaches each point Q in two
steps only through the unique line PQ, so no incidence (Q, PQ) can be deleted for any
member P != Q. The same argument covers the other arc-extension variants I considered,
so this family appears capped at 394 for d = 16. I did not find a construction here
that beats the record, so this program matches it rather than exceeding it, and it
does not use the time budget. Every output is checked with lib.is_valid, and the
fallback is K_{d,d}, which has diameter 2.
"""
import lib


def _is_prime(q):
    return q >= 2 and all(q % p for p in range(2, int(q ** 0.5) + 1))


def _pg_incidence(q):
    """Return (m, edges) for the incidence graph of PG(2, q), with m points and m lines."""
    n2, edges = lib.projective_plane_incidence(q)
    return n2 // 2, edges


def _conic_arc(q):
    """Point indices of a conic (plus nucleus for even q) in PG(2, q), q prime.

    The points (1, t, t^2) and (0, 0, 1) form an arc: every line meets them in <= 2 points.
    """
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, (t * t) % q)] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, S):
    """Add A_P (joined to the lines through P) and B_P (joined to the points on line P) for P in S."""
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        E.extend((a, m + L) for L in point_lines[P])
    for t, L in enumerate(S):
        b = 2 * m + k + t
        E.extend((Q, b) for Q in line_points[L])
    return 2 * m + 2 * k, E


def build(d, D, seed, time_limit):
    del seed, time_limit  # the construction is deterministic and finishes instantly
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
    for q in qs:
        m, edges = _pg_incidence(q)
        cands = [(2 * m, edges)]
        if d - q - 1 >= 2 and _is_prime(q):
            cands.append(_arc_graph(m, edges, _conic_arc(q)))
        for n_c, e_c in cands:
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
    return best
