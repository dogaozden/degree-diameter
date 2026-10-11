import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold attempt for D = 3: grow the arc-extended PG(2,q) graph by inserting
# new "twin-like" vertices whose neighbourhoods are taken from existing spare
# capacity. Adding one vertex x can never break an existing distance, so only
# x's own radius-3 ball needs checking (cheap). Removals are followed by a full
# diameter check, and any state that fails is rolled back.
#
# Fallbacks: K_{d,d} (valid for D >= 2) and the best valid arc graph.
# ----------------------------------------------------------------------------


def _pg(q):
    """Return (m, edges, pl, lp) for PG(2,q): points 0..m-1, lines m..2m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]   # point -> line indices
    lp = [[] for _ in range(m)]   # line index -> point indices
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _loads_ok(S, s, m, pl, lp):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_candidates(d, deadline, rng):
    """Arc-extended PG(2,q) graphs for prime powers q+1 <= d. Diameter 3. Sorted by order, largest first."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp = _pg(q)
        S = []
        if s >= 1:
            S = _greedy_arc(m, s, pl, lp, rng, 30, deadline)
        if s >= 2:
            F = lib.GF(q)
            pts = lib.projective_points(q)
            index = {p: i for i, p in enumerate(pts)}
            cs = _conic(q, index, F)
            if len(cs) > len(S) and _loads_ok(cs, s, m, pl, lp):
                S = cs
        if not _loads_ok(S, s, m, pl, lp):
            continue
        k = len(S)
        n = 2 * m + 2 * k
        E = list(edges)
        for t, P in enumerate(S):
            x = 2 * m + t
            for L in pl[P]:
                E.append((x, m + L))
        for t, j in enumerate(S):
            b = 2 * m + k + t
            for Q in lp[j]:
                E.append((Q, b))
        out.append((n, E, m, k))
    out.sort(key=lambda t: -t[0])
    return out


def _export(adj, alive):
    E = []
    for u in range(len(adj)):
        if alive[u]:
            for v in adj[u]:
                if u < v:
                    E.append((u, v))
    return E


def _valid_full(adj, alive, D):
    """Exact diameter check over alive vertices (bitmask BFS)."""
    N = len(adj)
    full = 0
    for v in range(N):
        if alive[v]:
            full |= 1 << v
    reach = [(1 << v) if alive[v] else 0 for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            if alive[v]:
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                new[v] = r
        reach = new
    for v in range(N):
        if alive[v] and reach[v] != full:
            return False
    return True


def _covers(adj, alive_n, N):
    """True if a new vertex adjacent to N reaches every alive vertex within distance 3."""
    lvl1 = set(N)
    lvl2 = set()
    for u in N:
        lvl2 |= adj[u]
    lvl2 -= lvl1
    reached = lvl1 | lvl2
    for w in lvl2:
        reached |= adj[w]
    return len(reached) == alive_n


def _insert_try(adj, col, alive, d, rng, cur):
    """Try to insert one new vertex built around a random existing vertex's neighbourhood."""
    n_idx = len(adj)
    c = rng.randrange(2)
    src = [u for u in range(n_idx) if alive[u] and col[u] == c and adj[u]]
    if not src:
        return False
    v = rng.choice(src)
    base = [u for u in adj[v] if len(adj[u]) < d]
    if len(base) < 2:
        return False
    bset = set(base)
    need = d - len(base)
    opp = [u for u in range(n_idx)
           if alive[u] and col[u] != c and len(adj[u]) < d and u not in bset]
    extra = rng.sample(opp, min(need, len(opp))) if need > 0 else []
    N = base + extra
    if not _covers(adj, cur, N):
        return False
    x = n_idx
    adj.append(set(N))
    for u in N:
        adj[u].add(x)
    col.append(c)
    alive.append(True)
    return True


def _grow(n0, E0, col0, d, rng, deadline):
    """Hill-climbing with removal and insertion, on a graph of diameter 3. Returns (best_n, best_E)."""
    adj = [set() for _ in range(n0)]
    for u, v in E0:
        adj[u].add(v)
        adj[v].add(u)
    col = list(col0)
    alive = [True] * n0
    cur = n0
    best_n, best_E = n0, list(E0)
    if all(len(s) >= d for s in adj):
        return best_n, best_E

    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_col = list(col)
        snap_alive = list(alive)
        snap_cur = cur

        alive_ids = [v for v in range(len(adj)) if alive[v]]
        k_rem = 1 if rng.random() < 0.7 else 2
        for r in rng.sample(alive_ids, k_rem):
            for u in adj[r]:
                adj[u].discard(r)
            adj[r] = set()
            alive[r] = False
            cur -= 1

        for _ in range(60):
            if _insert_try(adj, col, alive, d, rng, cur):
                cur += 1

        if cur >= snap_cur and _valid_full(adj, alive, 3):
            if cur > best_n:
                best_n = cur
                best_E = _export(adj, alive)
        else:
            adj[:] = snap_adj
            col[:] = snap_col
            alive[:] = snap_alive
            cur = snap_cur
    return best_n, best_E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.6 * time_limit
    deadline = start + budget

    if d < 1 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best_n, best_E = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_E

    rng = random.Random(seed * 1000003 + 97 * d + D)

    # Arc-extended projective plane graphs: diameter 3, hence valid for every D >= 3.
    cands = _arc_candidates(d, start + 0.2 * budget, rng)
    base = None
    for n, E, m, k in cands:
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E
            base = (n, E, m, k)
            break

    # Bold step (D = 3 only): grow the arc graph from spare capacity.
    if D == 3 and base is not None:
        n, E, m, k = base
        col = [0] * n
        for v in range(m, 2 * m):
            col[v] = 1
        for t in range(k):
            col[2 * m + k + t] = 1
        gn, gE = _grow(n, E, col, d, rng, deadline)
        if gn > best_n:
            rn, rE = lib.relabel(gE)
            if lib.is_valid(rn, rE, d, D):
                best_n, best_E = rn, rE

    if not lib.is_valid(best_n, best_E, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_E
