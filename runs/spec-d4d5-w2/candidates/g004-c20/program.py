import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bipartite regular graphs stored as side-indexed pairs (a, b):
#   A-vertex a is global id a, B-vertex b is global id s + b, with s = side size.
# Growth: vertex insertion (degree-preserving) followed by 2-switch annealing
# that minimises the number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad(s, pairs, D):
    """Ordered count of vertex pairs not within distance D (zero means valid)."""
    n = 2 * s
    adj = [[] for _ in range(n)]
    for a, b in pairs:
        adj[a].append(s + b)
        adj[s + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal(s, pairs, D, deadline, rng):
    """2-switch simulated annealing on `pairs` (mutated in place). True if cost reaches 0."""
    S = set(pairs)
    m = len(pairs)
    cost = _bad(s, pairs, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 3.0, 0.3
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = pairs[i]
        a2, b2 = pairs[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in S or n2 in S:
            continue
        pairs[i] = n1
        pairs[j] = n2
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(n1)
        S.add(n2)
        c2 = _bad(s, pairs, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            pairs[i] = (a1, b1)
            pairs[j] = (a2, b2)
            S.discard(n1)
            S.discard(n2)
            S.add((a1, b1))
            S.add((a2, b2))
    return cost == 0


def _insert(s, pairs, d, rng):
    """Add one A and one B vertex. Remove d edges with distinct ends (a_i, b_i);
    join new A-vertex to every b_i and new B-vertex to every a_i. Degrees stay d.
    Returns (s+1, new_pairs) or None."""
    m = len(pairs)
    chosen = None
    for _ in range(300):
        order = list(range(m))
        rng.shuffle(order)
        ua, ub, pick = set(), set(), []
        for idx in order:
            a, b = pairs[idx]
            if a in ua or b in ub:
                continue
            ua.add(a)
            ub.add(b)
            pick.append(idx)
            if len(pick) == d:
                break
        if len(pick) == d:
            chosen = pick
            break
    if chosen is None:
        return None
    cs = set(chosen)
    new = [p for k, p in enumerate(pairs) if k not in cs]
    for idx in chosen:
        a, b = pairs[idx]
        new.append((s, b))   # new A-vertex s -- old B-vertex b
        new.append((a, s))   # old A-vertex a -- new B-vertex s
    return s + 1, new


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe base: K_{d,d} (valid for D >= 2).
    base_s = d
    base_pairs = [(i, i) for i in range(d)]

    # Better base for D >= 3: PG(2,q) incidence with q = d-1 (degree d, diameter 3).
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        n2, edges = lib.projective_plane_incidence(d - 1)
        m = n2 // 2
        base_pairs = [(u, v - m) for u, v in edges]
        base_s = m

    best_s, best_pairs = base_s, list(base_pairs)

    if D >= 3:
        try:
            cur_s, cur_pairs = base_s, list(base_pairs)
            failures = 0
            while time.monotonic() < deadline:
                if 2 * (cur_s + 1) > lib.moore_bound(d, D):
                    break
                res = _insert(cur_s, cur_pairs, d, rng)
                if res is None:
                    break
                s2, p2 = res
                now = time.monotonic()
                rem = deadline - now
                step_dl = now + min(rem, max(1.5, 0.2 * rem))
                if _anneal(s2, p2, D, step_dl, rng):
                    cur_s, cur_pairs = s2, p2
                    best_s, best_pairs = s2, list(p2)
                    failures = 0
                else:
                    failures += 1
                    if failures >= 3:
                        break
        except Exception:
            pass

    n = 2 * best_s
    edges = [(a, best_s + b) for a, b in best_pairs]
    if lib.is_valid(n, edges, d, D):
        return n, edges

    # Final safety net.
    return lib.haar_graph(d, range(d))
