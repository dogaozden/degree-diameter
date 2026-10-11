import random
import time

import lib


# ----------------------------------------------------------------------------
# Decoupled arc search (new helper).
#
# Over PG(2, q) the left-new vertices x_P (P in S) are joined to the lines
# through P, and the right-new vertices y_L (L in T) are joined to the points
# on L. Line loads come only from S and point loads only from T, so S and T
# can be chosen independently. Each choice is a set with at most `cap` members
# in every constraint slot. _max_set grows such a set with random insertions,
# and single-blocker swaps move across plateaus.
# ----------------------------------------------------------------------------

def _max_set(slots, cap, deadline, rng):
    """Largest set X of elements such that every slot index c is used by at most cap members of X."""
    N = len(slots)
    C = 1 + max((c for s in slots for c in s), default=0)
    cnt = [0] * C
    inX = [False] * N
    X = []

    def blockers(e):
        bad = {c for c in slots[e] if cnt[c] >= cap}
        if not bad:
            return []
        return [f for f in X if any(c in bad for c in slots[f])]

    def add(e):
        inX[e] = True
        X.append(e)
        for c in slots[e]:
            cnt[c] += 1

    def rem(e):
        inX[e] = False
        X.remove(e)
        for c in slots[e]:
            cnt[c] -= 1

    order = list(range(N))
    rng.shuffle(order)
    for e in order:
        if not blockers(e):
            add(e)
    best = list(X)
    while time.monotonic() < deadline and N > 0:
        for _ in range(64):
            e = rng.randrange(N)
            if inX[e]:
                continue
            B = blockers(e)
            if not B:
                add(e)
            elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.05):
                for f in B:
                    rem(f)
                add(e)
            else:
                continue
            if len(X) > len(best):
                best = list(X)
    return best


def _arc_graph(q, s, dS, dT, rng):
    """Incidence graph of PG(2,q) plus x-vertices for an S-set of points and y-vertices for a T-set of lines."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]   # point -> line indices
    lp = [[] for _ in range(m)]   # line  -> point indices
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    S = _max_set(pl, s, dS, rng)
    T = _max_set(lp, s, dT, rng)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        E.extend((x, m + L) for L in pl[P])
    base = 2 * m + len(S)
    for t, L in enumerate(T):
        y = base + t
        E.extend((Q, y) for Q in lp[L])
    return 2 * m + len(S) + len(T), E


# ----------------------------------------------------------------------------
# Radius-2 cover growth (new helper, D = 3 only).
#
# A new vertex joined to a set N on one side keeps diameter 3 iff every vertex
# lies within distance 2 of N. Greedy set cover over radius-2 balls finds such
# N of size at most d among vertices with spare degree.
# ----------------------------------------------------------------------------

def _cover_grow(n, edges, d, deadline, rng):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s0 in range(n):
        if color[s0] != -1:
            continue
        color[s0] = 0
        st = [s0]
        while st:
            u = st.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    st.append(v)
    edges = list(edges)
    while time.monotonic() < deadline:
        b1 = []
        for v in range(n):
            x = 1 << v
            for u in adj[v]:
                x |= 1 << u
            b1.append(x)
        b2 = []
        for v in range(n):
            x = b1[v]
            for u in adj[v]:
                x |= b1[u]
            b2.append(x)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            pool = [s for s in range(n) if color[s] == c and len(adj[s]) < d]
            rng.shuffle(pool)
            unc = full
            chosen = []
            while unc and len(chosen) < d and pool:
                bs = max(pool, key=lambda s: (b2[s] & unc).bit_count())
                if (b2[bs] & unc) == 0:
                    break
                chosen.append(bs)
                unc &= ~b2[bs]
                pool.remove(bs)
            if unc == 0 and chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                added = True
                break
        if not added:
            break
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2 or d < 3:
        return lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective plane of largest order q with q + 1 <= d.
    q0 = next((q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)), None)
    if q0 is not None:
        n0, e0 = lib.projective_plane_incidence(q0)
        consider(n0, e0)

    # Arc-extended planes with spare degree s = d - q - 1 >= 1.
    qs = [(q, d - q - 1) for q in range(min(d - 1, 23), 1, -1)
          if lib.is_prime_power(q) and d - q - 1 >= 1]
    # Order by potential: most vertices first.
    qs.sort(key=lambda t: -(2 * (t[0] ** 2 + t[0] + 1) + 2 * ((t[1] - 1) * (t[0] + 1) + 1)))

    for idx, (q, s) in enumerate(qs):
        now = time.monotonic()
        if now >= end:
            break
        share = (end - now) / (len(qs) - idx)
        n, E = _arc_graph(q, s, now + 0.4 * share, now + 0.8 * share, rng)
        consider(n, E)
        if D == 3:
            n2, E2 = _cover_grow(n, E, d, now + 0.95 * share, rng)
            consider(n2, E2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
