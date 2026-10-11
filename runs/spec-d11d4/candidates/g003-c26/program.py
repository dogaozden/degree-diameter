import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective plane (D >= 3) and generalized quadrangle (D >= 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


def _pg_base(d):
    """PG(2, q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_base(d):
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 9 for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Helpers: bitmask balls, bipartition, set cover.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r (adj is a list of iterables)."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency collections."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate balls; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _cover_ls(cands, ball, full, d, rng, steps, deadline):
    """Swap-based local search for a cover of `full` by min(d, |cands|) candidate balls."""
    if not cands:
        return None
    k = min(d, len(cands))
    S = rng.sample(cands, k)
    in_s = set(S)

    def union(sel):
        u = 0
        for s in sel:
            u |= ball[s]
        return u

    cost = (full & ~union(S)).bit_count()
    for step in range(steps):
        if cost == 0:
            break
        if (step & 127) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        rest = S[:i] + S[i + 1:]
        miss = full & ~union(rest)
        best_t, best_g = None, -1
        for t in rng.sample(cands, min(30, len(cands))):
            if t in in_s:
                continue
            g = (ball[t] & miss).bit_count()
            if g > best_g:
                best_t, best_g = t, g
        if best_t is None:
            continue
        newcost = (miss & ~ball[best_t]).bit_count()
        if newcost <= cost or rng.random() < 0.02:
            in_s.discard(S[i])
            S[i] = best_t
            in_s.add(best_t)
            cost = newcost
    return S if cost == 0 else None


# ----------------------------------------------------------------------------
# Remove-and-repair iterated local search over vertex sets.
#
# State: adjacency sets over a growing id space, a liveness flag per id, a
# bipartition colour per id, the list of live added vertices, and the live count.
# Growth adds a vertex whose neighbourhood covers every live vertex within
# distance D-1 (monotone: never breaks validity). Perturbation deletes a few
# added vertices, which can break distances, so it is checked exactly.
# ----------------------------------------------------------------------------

def _copy_state(s):
    adj, live, color, added, n_live = s
    return ([set(x) for x in adj], list(live), list(color), list(added), n_live)


def _valid_live(adj, live, D):
    """True iff every pair of live vertices is within distance D in the live graph."""
    N = len(adj)
    ids = [v for v in range(N) if live[v]]
    full = 0
    for v in ids:
        full |= 1 << v
    reach = [(1 << v) if live[v] else 0 for v in range(N)]
    for _ in range(D):
        new = reach[:]
        for v in ids:
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return all(reach[v] == full for v in ids)


def _export(state):
    """Compact the live vertices to 0..n-1 and return (n, edges)."""
    adj, live, _, _, _ = state
    ids = [v for v in range(len(adj)) if live[v]]
    idx = {v: i for i, v in enumerate(ids)}
    edges = [(idx[v], idx[u]) for v in ids for u in adj[v] if u > v]
    return len(ids), edges


def _ils(base_n, base_edges, d, D, deadline, rng):
    """Grow a valid base graph by cover-additions, with remove-and-repair perturbations."""
    adj = [set() for _ in range(base_n)]
    for u, v in base_edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(base_n, adj)
    cur = (adj, [True] * base_n, color, [], base_n)
    best = _copy_state(cur)

    while time.monotonic() < deadline:
        adj, live, color, added, n_live = cur
        N = len(adj)
        ids = [v for v in range(N) if live[v]]
        full = 0
        for v in ids:
            full |= 1 << v
        ball = _balls_radius(N, adj, D - 1)

        grown = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in ids if color[s] == c and len(adj[s]) < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(3):
                if attempt == 0:
                    chosen = _greedy_cover(cands, ball, full, d, rng, False)
                elif attempt == 1:
                    chosen = _greedy_cover(cands, ball, full, d, rng, True)
                else:
                    chosen = _cover_ls(cands, ball, full, d, rng, 400, deadline)
                if chosen:
                    break
            if chosen:
                v = N
                adj.append(set())
                live.append(True)
                color.append(1 - c)
                for s in chosen:
                    adj[s].add(v)
                    adj[v].add(s)
                added.append(v)
                n_live += 1
                cur = (adj, live, color, added, n_live)
                grown = True
                break

        if grown:
            if n_live > best[4]:
                best = _copy_state(cur)
            continue

        if not added:
            break

        # Perturbation: remove a few added vertices, keep only if still valid.
        snap = _copy_state(cur)
        k = min(len(added), rng.choice([1, 1, 2, 2, 3, 5]))
        victims = rng.sample(added, k)
        for x in victims:
            for y in adj[x]:
                adj[y].discard(x)
            adj[x] = set()
            live[x] = False
        added = [a for a in added if live[a]]
        n_live -= k
        if _valid_live(adj, live, D):
            cur = (adj, live, color, added, n_live)
            if n_live < best[4] - 6:
                cur = _copy_state(best)
        else:
            cur = snap
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    try:
        bases = []
        if D >= 3:
            pg = _pg_base(d)
            if pg:
                bases.append(pg)
        if D >= 4:
            gq = _gq_base(d)
            if gq:
                bases.append(gq)
        bases.sort(key=lambda g: -g[0])

        base = None
        for n0, e0 in bases:
            if n0 > best_n and lib.is_valid(n0, e0, d, D):
                base = (n0, e0)
                break
        if base is None:
            base = (best_n, best[1])

        st = _ils(base[0], base[1], d, D, deadline, rng)
        n1, e1 = _export(st)
        if n1 > best_n and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)
            best_n = n1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
