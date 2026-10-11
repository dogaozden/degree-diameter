import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

T_HI = 2.0      # annealing temperature at the start of each cooling cycle
T_LO = 0.1      # temperature at the end of each cooling cycle
CYCLE = 1500    # iterations per cooling cycle (then reheat)


# ----------------------------------------------------------------------------
# Representation.
#
# A d-regular bipartite graph on h + h vertices is a list E of pairs (a, b),
# a, b in range(h). Vertex a is A-side vertex a; vertex b is B-side vertex h + b.
# Every vertex has degree d. The moves are degree-preserving double edge swaps,
# so every state is an exact d-regular bipartite graph (no duplicate edges).
#
# The objective is the number of unordered vertex pairs at distance > D.
# Zero means the graph is valid.
#
# Growth: from a valid graph on h + h vertices, insert one new A vertex and one
# new B vertex. Remove a matching of d edges (a_i, b_i), then add (new_A, b_i)
# and (a_i, new_B). Degrees are preserved. Then anneal until valid again.
# ----------------------------------------------------------------------------

def _cost(h, E, D):
    """Number of unordered vertex pairs at distance more than D (unreachable pairs included)."""
    n = 2 * h
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(h + b)
        adj[h + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        if nxt == reach:
            break
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _insert(h, E, d, rng):
    """Grow a valid d-regular bipartite graph on h+h vertices to h+1+h+1 vertices.

    Returns (newE, neweset), or None if no d-matching was found.
    """
    picked = None
    for _ in range(30):
        order = list(range(len(E)))
        rng.shuffle(order)
        used_a = set()
        used_b = set()
        cand = []
        for idx in order:
            a, b = E[idx]
            if a in used_a or b in used_b:
                continue
            used_a.add(a)
            used_b.add(b)
            cand.append(idx)
            if len(cand) == d:
                break
        if len(cand) == d:
            picked = cand
            break
    if picked is None:
        return None
    gone = set(picked)
    newE = [E[i] for i in range(len(E)) if i not in gone]
    for idx in picked:
        a, b = E[idx]
        newE.append((h, b))   # new A vertex joins old B vertex b
        newE.append((a, h))   # old A vertex a joins new B vertex
    return newE, set(newE)


def _anneal(h, E, eset, D, rng, deadline):
    """Double-edge-swap annealing on the cost. Returns the final cost (0 means valid)."""
    cur = _cost(h, E, D)
    t = 0
    while cur > 0 and time.monotonic() < deadline:
        phase = t % CYCLE
        temp = T_HI * (T_LO / T_HI) ** (phase / CYCLE)
        t += 1

        m = len(E)
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue

        E[i] = (a1, b2)
        E[j] = (a2, b1)
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add((a1, b2))
        eset.add((a2, b1))

        new = _cost(h, E, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = new
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            eset.discard((a1, b2))
            eset.discard((a2, b1))
            eset.add((a1, b1))
            eset.add((a2, b2))
    return cur


# ----------------------------------------------------------------------------
# Structured baselines and fallbacks.
# ----------------------------------------------------------------------------

def _pg_baseline(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if d <= 2:
        # Moore-optimal for d = 2: the cycle C_{2D}. For d = 1 the fallback K_2 is optimal.
        if d == 2:
            cyc = lib.haar_graph(D, [0, 1])
            if lib.is_valid(cyc[0], cyc[1], d, D) and cyc[0] > best[0]:
                best = cyc
        return best

    moore = lib.moore_bound(d, D)

    if D == 2:
        return best

    if D >= 3:
        pg = _pg_baseline(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    # Main search: unstructured d-regular bipartite graphs, grown one vertex
    # per side at a time and repaired by annealing.
    h = d
    E = [(a, b) for a in range(h) for b in range(h)]   # K_{d,d}
    eset = set(E)
    cur = 0

    while time.monotonic() < deadline:
        if cur == 0:
            n = 2 * h
            if n > best[0]:
                edges = [(a, h + b) for a, b in E]
                if lib.is_valid(n, edges, d, D):
                    best = (n, edges)
            if 2 * (h + 1) > moore:
                break
            res = _insert(h, E, d, rng)
            if res is None:
                break
            E, eset = res
            h += 1
        cur = _anneal(h, E, eset, D, rng, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
