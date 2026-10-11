import itertools
import math
import random
import time

import lib


def _is_prime(q):
    if q < 2:
        return False
    i = 2
    while i * i <= q:
        if q % i == 0:
            return False
        i += 1
    return True


def _gq_plus_matching(q):
    """Incidence graph of the generalized quadrangle W(q) for prime q (degree q+1, diameter 4),
    plus a perfect matching between points and lines to raise the degree to q+2.
    Adding edges never increases distances, so the diameter stays at most 4."""
    pts = []
    for v in itertools.product(range(q), repeat=4):
        if any(v) and next(x for x in v if x) == 1:
            pts.append(v)
    index = {p: i for i, p in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = pow(c, q - 2, q)
        return tuple((x * inv) % q for x in v)

    def form(x, y):
        # symplectic form on GF(q)^4
        return (x[0] * y[1] - x[1] * y[0] + x[2] * y[3] - x[3] * y[2]) % q

    lines = set()
    for i in range(P):
        p = pts[i]
        for j in range(i + 1, P):
            r = pts[j]
            if form(p, r) == 0:
                members = set()
                for a in range(q):
                    for b in range(q):
                        if a or b:
                            w = tuple((a * p[t] + b * r[t]) % q for t in range(4))
                            if any(w):
                                members.add(index[norm(w)])
                lines.add(frozenset(members))
    line_list = sorted((sorted(s) for s in lines))
    L = len(line_list)

    edges = []
    incident = [set() for _ in range(P)]
    for j, ms in enumerate(line_list):
        for i in ms:
            incident[i].add(j)
            edges.append((i, P + j))

    # Perfect matching between points and lines using only non-incident pairs (Kuhn's algorithm).
    match_line = [-1] * L

    def aug(i, seen):
        for j in range(L):
            if j in incident[i] or seen[j]:
                continue
            seen[j] = True
            if match_line[j] == -1 or aug(match_line[j], seen):
                match_line[j] = i
                return True
        return False

    for i in range(P):
        if not aug(i, [False] * L):
            return None
    for j in range(L):
        edges.append((match_line[j], P + j))
    return P + L, edges


def _groups_by_order(maxn):
    """Table: order -> list of (m, k, r) giving semidirect groups Z_m x| Z_k of that order."""
    table = {}
    for m in range(1, maxn + 1):
        for k in range(1, maxn // m + 1):
            order = m * k
            if m == 1:
                rs = [0]
            else:
                rs = [r for r in range(1, m)
                      if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            for r in rs:
                table.setdefault(order, []).append((m, k, r))
    return table


def _lift_search(d, D, rng, deadline, best_n, table, moore):
    """Random voltage lifts of small bipartite base multigraphs over small groups.
    Returns the largest found (n, edges) that beats best_n, or None."""
    found = None

    def pairs_for(bn):
        out = []
        for b in range(1, 5):
            for o in range(bn // (2 * b) + 1, moore // (2 * b) + 1):
                if o in table:
                    out.append((b, o))
        return out

    pairs = pairs_for(best_n)
    while pairs and time.monotonic() < deadline:
        b, o = rng.choice(pairs)
        m, k, r = rng.choice(table[o])
        order, mul, _ = lib.semidirect_group(m, k, r)
        # Base: b vertices on side A (0..b-1), b on side B (b..2b-1), d-regular bipartite multigraph.
        a_list = [u for u in range(b) for _ in range(d)]
        b_list = [b + v for v in range(b) for _ in range(d)]
        rng.shuffle(b_list)
        darts = [(u, v, rng.randrange(order)) for u, v in zip(a_list, b_list)]
        n, edges = lib.group_lift(2 * b, darts, order, mul)
        if n > best_n and lib.within_diameter(n, edges, D):
            best_n = n
            found = (n, edges)
            pairs = pairs_for(best_n)
    return found


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.72 * time_limit)
    rng = random.Random(seed)
    best = None

    def consider(res):
        nonlocal best
        if res is None:
            return False
        n, edges = res
        if best is not None and n <= best[0]:
            return False
        try:
            ok = lib.is_valid(n, edges, d, D)
        except Exception:
            ok = False
        if ok:
            best = (n, edges)
        return ok

    # Safe fallback: K_{d,d}, valid whenever D >= 2.
    try:
        consider(lib.haar_graph(d, range(d)))
    except Exception:
        pass

    try:
        # D = 3 with d-1 a prime power: projective plane incidence meets the Moore bound.
        if D == 3 and lib.is_prime_power(d - 1):
            consider(lib.projective_plane_incidence(d - 1))
            if best is not None:
                return best

        # D = 4 with q = d-2 prime: generalized quadrangle W(q) plus a matching (new construction).
        if D == 4 and _is_prime(d - 2):
            consider(_gq_plus_matching(d - 2))

        # Remaining time: random group-lift search for something larger than the current best.
        moore = lib.moore_bound(d, D)
        maxn = min(moore // 2, 400)
        if maxn >= 1 and time.monotonic() < deadline:
            table = _groups_by_order(maxn)
            best_n = best[0] if best is not None else 0
            res = _lift_search(d, D, rng, deadline, best_n, table, moore)
            consider(res)
    except Exception:
        pass

    if best is None:
        return 1, []
    return best
