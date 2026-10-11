import random
import time
import lib


def _pack(item_groups, group_items, s, rng, deadline):
    """Randomized local search for copy counts a[i] with sum over groups of each item's load <= s.

    item_groups[i]: groups touched by item i; group_items[g]: items touched by group g.
    Returns the best count vector found (maximising total count).
    """
    n_items = len(item_groups)
    a = [0] * n_items
    load = [0] * len(group_items)
    total = 0
    best_total = 0
    best = a[:]
    it = 0
    while True:
        it += 1
        if (it & 127) == 0 and time.monotonic() >= deadline:
            break
        p = rng.randrange(n_items)
        gs = item_groups[p]
        full = [g for g in gs if load[g] >= s]
        if not full:
            a[p] += 1
            for g in gs:
                load[g] += 1
            total += 1
            if total > best_total:
                best_total = total
                best = a[:]
        elif len(full) == 1:
            # Plateau move: free one unit on the single full group by removing a copy
            # of some other item r on it, then add one copy of p. Total unchanged.
            cands = [r for r in group_items[full[0]] if r != p and a[r] > 0]
            if cands:
                r = rng.choice(cands)
                a[r] -= 1
                for g in item_groups[r]:
                    load[g] -= 1
                a[p] += 1
                for g in gs:
                    load[g] += 1
    return best


def _pg_extended(d, q, rng, deadline_a, deadline_b):
    """PG(2,q) incidence plus new point copies (on full pencils) and new line copies (on full lines).

    Every new point sees all lines through one old point; every new line sees all points of one
    old line. Diameter stays 3 and the graph stays bipartite (points + new points vs lines + new lines).
    """
    n0, inc = lib.projective_plane_incidence(q)
    m = n0 // 2
    pl = [[] for _ in range(m)]   # point -> lines through it
    lp = [[] for _ in range(m)]   # line -> points on it
    for u, v in inc:
        pl[u].append(v - m)
        lp[v - m].append(u)
    s = d - (q + 1)               # spare degree on every old vertex
    a = _pack(pl, lp, s, rng, deadline_a)   # new points on pencils of old points
    b = _pack(lp, pl, s, rng, deadline_b)   # new lines on point sets of old lines
    edges = [(int(u), int(v)) for u, v in inc]
    nxt = n0
    for P, cnt in enumerate(a):
        for _ in range(cnt):
            for L in pl[P]:
                edges.append((nxt, m + L))
            nxt += 1
    for L, cnt in enumerate(b):
        for _ in range(cnt):
            for P in lp[L]:
                edges.append((P, nxt))
            nxt += 1
    return nxt, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)
    if D == 3:
        q = next((x for x in range(d - 1, 1, -1) if lib.is_prime_power(x)), None)
        if q is not None:
            try:
                n, edges = _pg_extended(d, q, rng,
                                        start + 0.35 * time_limit,
                                        start + 0.65 * time_limit)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass
            n0, e0 = lib.projective_plane_incidence(q)
            if lib.is_valid(n0, e0, d, D):
                return n0, e0

    # Generic fallback: Haar graph search.
    deadline = start + 0.8 * time_limit
    best = lib.haar_graph(d, range(d))  # complete bipartite K_{d,d}: always valid
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best
