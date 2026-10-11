import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: instead of algebraic constructions, grow a d-regular bipartite
# graph one vertex pair at a time from K_{d,d}. Each insertion keeps regularity
# (remove a matching of d edges, route them through a new left and right vertex),
# then simulated annealing with 2-switch moves repairs the diameter. The cost is
# the number of vertex pairs farther apart than D, computed with bitsets.
# ----------------------------------------------------------------------------


def _sa_cost(s, E, D):
    """Number of unordered vertex pairs at distance > D. Left vertex a is a, right b is s + b."""
    n = 2 * s
    adj = [[] for _ in range(n)]
    for a, b in E:
        v = s + b
        adj[a].append(v)
        adj[v].append(a)
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


def _anneal(s, E, D, rng, deadline, steps, T0=1.5, T1=0.15):
    """Anneal 2-switch moves on E in place. Returns True iff the diameter bound holds."""
    present = set(E)
    cur = _sa_cost(s, E, D)
    if cur == 0:
        return True
    m = len(E)
    for t in range(steps):
        if (t & 15) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (t / steps)
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in present or (a2, b1) in present:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        present.discard((a1, b1))
        present.discard((a2, b2))
        present.add((a1, b2))
        present.add((a2, b1))
        c2 = _sa_cost(s, E, D)
        if c2 <= cur or rng.random() < math.exp((cur - c2) / T):
            cur = c2
            if cur == 0:
                return True
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            present.discard((a1, b2))
            present.discard((a2, b1))
            present.add((a1, b1))
            present.add((a2, b2))
    return False


def _insert(s, E, d, rng):
    """Add one left vertex s and one right vertex s to a d-regular graph, keeping it d-regular.

    Pick a matching of d edges (a_k, b_k); replace each by (s, b_k) and (a_k, s).
    Returns the new edge list, or None if no matching of size d is found.
    """
    idxs = list(range(len(E)))
    rng.shuffle(idxs)
    ua, ub, chosen = set(), set(), []
    for idx in idxs:
        a, b = E[idx]
        if a in ua or b in ub:
            continue
        ua.add(a)
        ub.add(b)
        chosen.append(idx)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    cs = set(chosen)
    out = [E[i] for i in range(len(E)) if i not in cs]
    new = s  # index of the new left vertex and of the new right vertex
    for idx in chosen:
        a, b = E[idx]
        out.append((new, b))
        out.append((a, new))
    return out


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is d-regular.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    # Algebraic Moore graph when d - 1 is a prime power and D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed)

    # Start from K_{d,d} (valid), grow by vertex pairs, repair by annealing.
    s_best = d
    E_best = [(a, b) for a in range(d) for b in range(d)]
    phase_cap = max(0.5, budget / 5.0)
    steps = 2000

    while time.monotonic() < deadline:
        if 2 * (s_best + 1) > moore:
            break
        cand = _insert(s_best, E_best, d, rng)
        if cand is None:
            break
        s = s_best + 1
        E = cand
        phase_deadline = min(deadline, time.monotonic() + phase_cap)
        if _anneal(s, E, D, rng, phase_deadline, steps):
            s_best = s
            E_best = list(E)

    n = 2 * s_best
    edges = [(a, s_best + b) for a, b in E_best]
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return fallback
