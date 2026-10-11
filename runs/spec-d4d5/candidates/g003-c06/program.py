import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: generalized quadrangle W(q) and projective plane incidence graphs.
# ----------------------------------------------------------------------------

def _gq_base(q):
    """Incidence graph of points and lines of W(q) (diameter 4, (q+1)-regular)."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _as_bip(n, edges, d):
    """Return (s, E) with E a list of [a, b] (a in A = 0..s-1, b in B = 0..s-1) if the
    graph is d-regular with equal sides, else None."""
    if n % 2:
        return None
    s = n // 2
    deg = [0] * n
    E = []
    for u, v in edges:
        if u < s <= v:
            a, b = u, v - s
        elif v < s <= u:
            a, b = v, u - s
        else:
            return None
        E.append([a, b])
        deg[u] += 1
        deg[v] += 1
    if any(x != d for x in deg):
        return None
    if len({(a, b) for a, b in E}) != len(E):
        return None
    return s, E


# ----------------------------------------------------------------------------
# Bipartite regular graphs as (s, E): A-vertex i -> i, B-vertex j -> s + j.
# Engine: vertex-insertion growth and Z_2 doubling lifts, repaired by
# double-edge-switch simulated annealing on the number of pairs at distance > D.
# ----------------------------------------------------------------------------

def _adj(s, E):
    adj = [[] for _ in range(2 * s)]
    for a, b in E:
        y = s + b
        adj[a].append(y)
        adj[y].append(a)
    return adj


def _bad(s, adj, D):
    """Number of unordered vertex pairs at distance > D (bitset BFS)."""
    N = 2 * s
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


def _lift(s0, E0, rng):
    """Random Z_2 voltage lift of a bipartite base: doubles s."""
    E2 = []
    for a, b in E0:
        g = rng.randrange(2)
        for c in (0, 1):
            E2.append([a + s0 * c, b + s0 * ((c + g) % 2)])
    return 2 * s0, E2


def _insert(s, d, E, rng):
    """Add one vertex per side; remove d-1 edges with distinct endpoints and re-attach them.
    Degrees stay d and the graph stays bipartite."""
    order = list(range(len(E)))
    rng.shuffle(order)
    usedA, usedB, chosen = set(), set(), []
    for idx in order:
        a, b = E[idx]
        if a in usedA or b in usedB:
            continue
        chosen.append(idx)
        usedA.add(a)
        usedB.add(b)
        if len(chosen) == d - 1:
            break
    if len(chosen) < d - 1:
        return None
    cs = set(chosen)
    newE = [e for k, e in enumerate(E) if k not in cs]
    na = s
    nb = s
    newE.append([na, nb])
    for idx in chosen:
        a, b = E[idx]
        newE.append([na, b])
        newE.append([a, nb])
    return s + 1, newE


def _anneal(s, d, D, E0, rng, deadline, iters):
    """Double-edge switches (preserve degrees, bipartiteness, simplicity) minimising bad pairs.
    Returns the edge list on success, else None."""
    E = [[a, b] for a, b in E0]
    m = len(E)
    Es = set((a, b) for a, b in E)
    cost = _bad(s, _adj(s, E), D)
    T0, T1 = 2.0, 0.1
    for it in range(iters):
        if cost == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            return None
        T = T0 * (T1 / T0) ** (it / iters)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in Es or (a2, b1) in Es:
            continue
        E[i] = [a1, b2]
        E[j] = [a2, b1]
        Es.discard((a1, b1))
        Es.discard((a2, b2))
        Es.add((a1, b2))
        Es.add((a2, b1))
        new = _bad(s, _adj(s, E), D)
        if new <= cost or rng.random() < math.exp((cost - new) / T):
            cost = new
        else:
            E[i] = [a1, b1]
            E[j] = [a2, b2]
            Es.discard((a1, b2))
            Es.discard((a2, b1))
            Es.add((a1, b1))
            Es.add((a2, b2))
    return E if cost == 0 else None


LIFT_ITERS = 3000
GROW_ITERS = 3000


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2), valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        return (2, [(0, 1)]) if d >= 1 and D >= 1 else (1, [])

    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D, order 2D.
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D) and n > best[0]:
            return n, cyc
        return best
    if d < 3:
        return best

    # Choose the largest valid d-regular bipartite base with diameter <= D.
    q = d - 1
    bases = []
    if lib.is_prime_power(q):
        if D >= 4:
            bases.append(_gq_base(q))
        if D >= 3:
            bases.append(lib.projective_plane_incidence(q))
    bases.append(lib.haar_graph(d, range(d)))

    chosen = None
    for n, e in bases:
        conv = _as_bip(n, e, d)
        if conv is None:
            continue
        s, E = conv
        if _bad(s, _adj(s, E), D) != 0:
            continue
        if chosen is None or s > chosen[0]:
            chosen = (s, E)
    if chosen is None:
        return best

    s0, E0 = chosen
    cur_s, cur_E = s0, E0
    s_limit = lib._moore_bound(d, D) // 2

    # Stage 1: Z_2 doubling lifts repaired by annealing.
    if 2 * s0 <= s_limit:
        lift_deadline = time.monotonic() + 0.5 * max(0.0, deadline - time.monotonic())
        while time.monotonic() < lift_deadline:
            s2, E2 = _lift(s0, E0, rng)
            res = _anneal(s2, d, D, E2, rng, lift_deadline, LIFT_ITERS)
            if res is not None:
                cur_s, cur_E = s2, res
                break

    # Stage 2: vertex-insertion growth with annealing repair.
    while time.monotonic() < deadline and cur_s + 1 <= s_limit:
        ins = _insert(cur_s, d, cur_E, rng)
        if ins is None:
            break
        s2, E2 = ins
        res = _anneal(s2, d, D, E2, rng, deadline, GROW_ITERS)
        if res is not None:
            cur_s, cur_E = s2, res

    n_out = 2 * cur_s
    edges = [(a, cur_s + b) for a, b in cur_E]
    if cur_s > s0 and lib.is_valid(n_out, edges, d, D) and n_out > best[0]:
        return n_out, edges
    return best
