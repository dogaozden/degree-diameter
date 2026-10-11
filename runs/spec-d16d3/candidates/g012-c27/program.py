import math
import random
import time

import lib


def _bad_pairs(N, adj, D):
    """Number of unordered vertex pairs at distance greater than D (adj: list of sets)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _pg_arc_base(d):
    """PG(2,q) incidence (q the largest prime power with q+1 <= d) plus, when spare >= 2,
    one A-vertex per conic point (on its lines) and one B-vertex per conic line (on its points).

    Diameter 3 holds for any point set S, since the only constraints are degree constraints.
    Returns (n, edges, colors) with colors[v] in {0, 1} giving the bipartition, or None.
    """
    q = next((c for c in range(d - 1, 1, -1) if lib.is_prime_power(c)), None)
    if q is None:
        return None
    n2, pg_edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    s = d - q - 1
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in pg_edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    edges = [(u, v) for u, v in pg_edges]
    colors = [0] * m + [1] * m
    n = 2 * m
    if s >= 2:
        F = lib.GF(q)
        index = {p: i for i, p in enumerate(lib.projective_points(q))}
        S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        if q % 2 == 0:
            S.append(index[(0, 1, 0)])
        cl = [0] * m
        cp = [0] * m
        for P in S:
            for L in point_lines[P]:
                cl[L] += 1
            for Q in line_points[P]:
                cp[Q] += 1
        if max(cl) <= s and max(cp) <= s:
            k = len(S)
            colors += [0] * k + [1] * k
            for t, P in enumerate(S):
                x = n + t
                edges.extend((x, m + L) for L in point_lines[P])
            for t, P in enumerate(S):
                b = n + k + t
                edges.extend((Q, b) for Q in line_points[P])
            n += 2 * k
    return n, edges, colors


def _anneal(N, adj, colors, d, D, deadline, rng, iters):
    """Simulated annealing on the bad-pair count. Mutates adj in place. Returns True iff cost reaches 0.

    Moves: add a missing edge between spare opposite-colour vertices (never increases cost),
    or relocate one endpoint of a random edge to another spare vertex of the same side.
    """
    cost = _bad_pairs(N, adj, D)
    E = [(u, v) for u in range(N) if colors[u] == 0 for v in adj[u]]
    for it in range(iters):
        if cost == 0:
            return True
        if time.monotonic() > deadline or not E:
            break
        T = 1.0 * (0.03 ** (it / iters))
        S0 = [v for v in range(N) if colors[v] == 0 and len(adj[v]) < d]
        S1 = [v for v in range(N) if colors[v] == 1 and len(adj[v]) < d]
        if not S0 or not S1:
            break
        if rng.random() < 0.3:
            for _ in range(20):
                x = rng.choice(S0)
                y = rng.choice(S1)
                if y not in adj[x]:
                    adj[x].add(y)
                    adj[y].add(x)
                    E.append((x, y))
                    cost = _bad_pairs(N, adj, D)
                    break
            continue
        idx = rng.randrange(len(E))
        a, b = E[idx]
        if rng.random() < 0.5:
            cands = [x for x in S0 if x != a and x not in adj[b]]
            if not cands:
                continue
            na, nb = rng.choice(cands), b
        else:
            cands = [y for y in S1 if y != b and y not in adj[a]]
            if not cands:
                continue
            na, nb = a, rng.choice(cands)
        adj[a].discard(b)
        adj[b].discard(a)
        adj[na].add(nb)
        adj[nb].add(na)
        c2 = _bad_pairs(N, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            E[idx] = (na, nb)
        else:
            adj[na].discard(nb)
            adj[nb].discard(na)
            adj[a].add(b)
            adj[b].add(a)
    return cost == 0


def _grow(N, adj, colors, d, D, deadline, rng):
    """Repeatedly add one vertex (either side) and anneal until diameter D is restored."""
    while time.monotonic() < deadline:
        grew = False
        for c in rng.sample([0, 1], 2):
            now = time.monotonic()
            if now >= deadline:
                break
            nadj = [set(a) for a in adj]
            nadj.append(set())
            ncol = colors + [c]
            x = N
            cands = [v for v in range(N) if ncol[v] == 1 - c and len(nadj[v]) < d]
            if not cands:
                continue
            rng.shuffle(cands)
            for v in cands[:d]:
                nadj[x].add(v)
                nadj[v].add(x)
            att_deadline = now + 0.5 * (deadline - now)
            if _anneal(N + 1, nadj, ncol, d, D, att_deadline, rng, 6000):
                adj, colors, N = nadj, ncol, N + 1
                grew = True
                break
        if not grew:
            break
    return N, adj, colors


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback

    if D >= 3 and d >= 3:
        try:
            base = _pg_arc_base(d)
            if base is not None:
                n, e, colors = base
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                if D == 3 and d >= 4:
                    adj = [set() for _ in range(n)]
                    for u, v in e:
                        adj[u].add(v)
                        adj[v].add(u)
                    N, adj2, _ = _grow(n, adj, colors, d, D, deadline, rng)
                    if N > best[0]:
                        e2 = [(u, v) for u in range(N) for v in adj2[u] if u < v]
                        if lib.is_valid(N, e2, d, D):
                            best = (N, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
