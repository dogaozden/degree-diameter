import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: incidence graph of PG(2, q), the Araujo-Pardo & Lopez record graph,
# and K_{d,d} as a universal fallback.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Record graph of order 2(q^2+q+5), degree q+2, for q = d-2 a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


# ----------------------------------------------------------------------------
# New idea: degree-preserving "pair insertion" with annealed repair.
#
# Insert two new vertices v (side 0) and w (side 1), each of degree d.
# Pick a matching of d edges (a_i, b_i) (a_i side 0, b_i side 1), delete them,
# and add v-b_i and w-a_i. Every old vertex keeps its degree, the graph stays
# bipartite, and the order grows by 2. Diameter is then usually broken, so we
# repair with degree-preserving 2-switches (a,b),(c,e) -> (a,e),(c,b), annealing
# on the number of vertex pairs at distance > D. The move is accepted only
# when the repaired graph has zero bad pairs.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (adj: list of sets)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _insert_pair(n, E, d, rng):
    """Insert v (side 0) and w (side 1) by rerouting a d-matching. Returns (n+2, E') or None.

    E stores every edge as (side0, side1).
    """
    order = list(range(len(E)))
    rng.shuffle(order)
    used_a, used_b, chosen = set(), set(), []
    for idx in order:
        a, b = E[idx]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(idx)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    v, w = n, n + 1
    cs = set(chosen)
    newE = [E[i] for i in range(len(E)) if i not in cs]
    for idx in chosen:
        a, b = E[idx]
        newE.append((v, b))   # v side 0, b side 1
        newE.append((a, w))   # a side 0, w side 1
    return n + 2, newE


def _repair(n, E, D, rng, deadline, iters):
    """Anneal degree-preserving 2-switches on E (in place) until diameter <= D. True on success."""
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    cost = _bad(n, adj, D)
    m = len(E)
    T0, T_end = 1.0, 0.05
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T_end / T0) ** (it / max(1, iters))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _bad(n, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E[i] = (a, e)
            E[j] = (c, b)
            cost = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cost == 0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Candidate bases; keep the largest valid one.
    cands = [lib.haar_graph(d, range(d))]          # K_{d,d}, diameter 2
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            cands.append(pg)
        ar = _araujo(d)
        if ar is not None:
            cands.append(ar)

    base = None
    for n0, E0 in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n0, E0, d, D):
            base = (n0, [tuple(e) for e in E0])
            break
    if base is None:
        return lib.haar_graph(d, range(d))

    n, E = base[0], list(base[1])
    best = (n, list(E))

    # Orient every edge as (side0, side1) so the insertion/switch invariants hold.
    adj0 = [[] for _ in range(n)]
    for u, v in E:
        adj0[u].append(v)
        adj0[v].append(u)
    color = _bipartition(n, adj0)
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in E]

    # Insertion + repair growth, restarting from the last valid graph on failure.
    if d >= 2 and D >= 2:
        while time.monotonic() < deadline:
            ins = _insert_pair(n, E, d, rng)
            if ins is None:
                break
            n2, E2 = ins
            if _repair(n2, E2, D, rng, deadline, iters=1500):
                n, E = n2, E2
                best = (n, list(E))

    # Final verification with a fallback to a guaranteed-valid graph.
    if lib.is_valid(best[0], best[1], d, D):
        return best
    return base[0], list(base[1]) if lib.is_valid(base[0], base[1], d, D) else lib.haar_graph(d, range(d))
