"""Bold variant for D >= 4: twin blow-up of the parabolic quadric Q(4,q).

Construction (q = d - 2 prime, so the base has degree q + 1 = d - 1 and one spare
slot per vertex):
  1. Base: incidence graph of Q(4,q), a generalized quadrangle of order (q,q).
     It has 2(q+1)(q^2+1) vertices, degree q+1, diameter 4, and is bipartite.
  2. Twin points of an ovoid O of Q(4,q). Each line then receives exactly one
     twin, so every line reaches degree d.
  3. Twin lines of a partial spread found by local search. Each point receives at
     most one twin, so every point stays within degree d.
  4. Greedy twinning of any vertex whose neighbours still have spare degree,
     then saturation with edges between spare opposite-side vertices.

A twin has the same neighbourhood as its original, and edges are never removed,
so distances never grow and bipartiteness is kept. Every output is checked with
lib.is_valid, with K_{d,d} as the fallback.

Honest ceiling: with the largest partial spread of size q^2 - q + 1 (believed to
be the Tallini bound for q odd), this family reaches about 359 for d = 7, which
ties the parent rather than beating the record. This is a high-risk exploration
of a different construction; any gain beyond the ceiling needs a larger partial
spread or a further extension step.
"""
import itertools
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


def _norm(v, q):
    c = next(x for x in v if x)
    inv = pow(c, q - 2, q)
    return tuple((x * inv) % q for x in v)


def _quadric(q):
    """Points and lines of Q(4,q) for an odd prime q: x0x1 + x2x3 + x4^2 = 0."""
    pts = sorted({_norm(v, q) for v in itertools.product(range(q), repeat=5)
                  if any(v) and (v[0] * v[1] + v[2] * v[3] + v[4] * v[4]) % q == 0})
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[1] + x[1] * y[0] + x[2] * y[3] + x[3] * y[2] + 2 * x[4] * y[4]) % q

    P = len(pts)
    lines = set()
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            y = pts[j]
            if bil(x, y):
                continue
            L = set()
            for t in range(q):
                v = tuple((x[k] + t * y[k]) % q for k in range(5))
                L.add(index[_norm(v, q)])
            L.add(index[y])
            lines.add(tuple(sorted(L)))
    return pts, sorted(lines)


def _ovoid(q, pts, lines):
    """Ovoid of Q(4,q): a hyperplane section meeting every line in exactly one point."""
    hyper = sorted({_norm(a, q) for a in itertools.product(range(q), repeat=5) if any(a)})
    for a in hyper:
        S = {i for i, p in enumerate(pts)
             if sum(a[k] * p[k] for k in range(5)) % q == 0}
        if len(S) != q * q + 1:
            continue
        if all(sum(1 for p in L if p in S) == 1 for L in lines):
            return sorted(S)
    return None


def _partial_spread(lines, P, deadline, rng):
    """Largest set of lines with pairwise disjoint point sets, by local search."""
    m = len(lines)
    owner = [-1] * P
    chosen = set()

    def add(i):
        chosen.add(i)
        for u in lines[i]:
            owner[u] = i

    def remove(i):
        chosen.discard(i)
        for u in lines[i]:
            if owner[u] == i:
                owner[u] = -1

    order = list(range(m))
    rng.shuffle(order)
    for i in order:
        if all(owner[u] < 0 for u in lines[i]):
            add(i)
    best = set(chosen)

    while time.monotonic() < deadline:
        i = rng.randrange(m)
        if i in chosen:
            continue
        conf = {owner[u] for u in lines[i] if owner[u] >= 0}
        if len(conf) <= 1 or (len(conf) == 2 and rng.random() < 0.02):
            for j in list(conf):
                remove(j)
            add(i)
            if len(chosen) > len(best):
                best = set(chosen)
        elif chosen and rng.random() < 0.001:
            remove(rng.choice(list(chosen)))
    return sorted(best)


def _saturate(n, adj, side, d, rng):
    left = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _grow(adj, side, d, rng, deadline):
    """Twin any vertex whose neighbours all have spare degree, then saturate."""
    for _ in range(6):
        if time.monotonic() > deadline:
            break
        grew = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if all(len(adj[u]) < d for u in nb):
                w = len(adj)
                adj.append(set(nb))
                side.append(side[v])
                for u in nb:
                    adj[u].add(w)
                grew = True
        _saturate(len(adj), adj, side, d, rng)
        if not grew:
            break
    return adj, side


def _build_gq_twin(d, deadline, rng):
    q = d - 2
    if q < 3 or not _is_prime(q):
        return None
    pts, lines = _quadric(q)
    P, L = len(pts), len(lines)
    n = P + L
    adj = [set() for _ in range(n)]
    for j, Ls in enumerate(lines):
        for i in Ls:
            adj[i].add(P + j)
            adj[P + j].add(i)
    side = [0] * P + [1] * L

    twins = []
    ov = _ovoid(q, pts, lines)
    if ov is not None:
        twins.extend(ov)  # point twins: each line gets exactly one
    twins.extend(P + j for j in _partial_spread(lines, P, deadline, rng))

    # Twins take base neighbourhoods; base adjacency is not changed by twinning.
    for v in twins:
        w = len(adj)
        adj.append(set(adj[v]))
        side.append(side[v])
        for u in adj[v]:
            adj[u].add(w)

    _saturate(len(adj), adj, side, d, rng)
    adj, side = _grow(adj, side, d, rng, deadline)
    n = len(adj)
    edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite with degree d.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        if D == 3 and lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
        if D >= 4:
            res = _build_gq_twin(d, deadline, rng)
            if res is not None:
                consider(*res)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
