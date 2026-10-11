import itertools
import random
import time

import lib


_GW_CACHE = {}


def _gw(q):
    """Incidence graph of points and lines of W(q), a generalized quadrangle. Returns (n, edges, P)."""
    if q in _GW_CACHE:
        return _GW_CACHE[q]
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    res = (2 * P, edges, P)
    _GW_CACHE[q] = res
    return res


def _state_from_edges(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    m = n // 2
    color = [0 if v < m else 1 for v in range(n)]
    return adj, color


def _perfect_matching(n, adj, color, rng):
    left = [v for v in range(n) if color[v] == 0]
    rng.shuffle(left)
    match_r = {}
    match_l = {}

    def try_aug(u, seen):
        nb = list(adj[u])
        rng.shuffle(nb)
        for w in nb:
            if w in seen:
                continue
            seen.add(w)
            if w not in match_r or try_aug(match_r[w], seen):
                match_r[w] = u
                match_l[u] = w
                return True
        return False

    for u in left:
        if not try_aug(u, set()):
            return None
    return [(u, match_l[u]) for u in left]


def _base_graph(q, d, rng):
    """W(q) with a random (q+1-d)-factor removed, giving a d-regular bipartite base."""
    n, edges, P = _gw(q)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = [0 if v < P else 1 for v in range(n)]
    for _ in range((q + 1) - d):
        M = _perfect_matching(n, adj, color, rng)
        if M is None:
            return None
        for u, v in M:
            adj[u].discard(v)
            adj[v].discard(u)
    return adj, color


def _balls(adj, alive_list, r):
    ball = [0] * len(adj)
    for v in alive_list:
        ball[v] = 1 << v
    for _ in range(r):
        new = [0] * len(adj)
        for v in alive_list:
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return ball


def _kill(adj, alive, x):
    alive[x] = False
    for u in adj[x]:
        adj[u].discard(x)
    adj[x] = set()


def _repair(adj, alive, D, rng, end):
    """Greedily delete the vertex with the most pairs at distance > D until no such pair remains."""
    while True:
        if time.monotonic() > end:
            return False
        alive_list = [v for v in range(len(adj)) if alive[v]]
        if not alive_list:
            return True
        ball = _balls(adj, alive_list, D)
        full = 0
        for v in alive_list:
            full |= 1 << v
        vals = [(full & ~ball[v]).bit_count() for v in alive_list]
        if sum(vals) == 0:
            return True
        top = max(vals)
        cands = [v for v, b in zip(alive_list, vals) if b == top]
        _kill(adj, alive, rng.choice(cands))


def _cover(cands, ball, full, d, rng):
    covered = 0
    chosen = []
    pool = list(cands)
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        mx = max(gains)
        if mx == 0:
            break
        idx = [i for i, g in enumerate(gains) if g == mx]
        s = pool.pop(rng.choice(idx))
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _fill(adj, color, alive, d, D, rng):
    """Add vertices whose neighbourhoods cover everything within distance D-1 (keeps diameter <= D)."""
    while True:
        n = len(adj)
        alive_list = [v for v in range(n) if alive[v]]
        full = 0
        for v in alive_list:
            full |= 1 << v
        ball = _balls(adj, alive_list, D - 1)
        sides = [0, 1]
        rng.shuffle(sides)
        placed = False
        for c in sides:
            cands = [s for s in alive_list if color[s] == 1 - c and len(adj[s]) < d]
            if not cands:
                continue
            chosen = _cover(cands, ball, full, d, rng)
            if chosen is None:
                continue
            v = n
            adj.append(set())
            color.append(c)
            alive.append(True)
            for s in chosen:
                adj[s].add(v)
                adj[v].add(s)
            placed = True
            break
        if not placed:
            return


def _saturate(adj, color, alive, d, rng):
    """Add cross-side edges between spare-degree vertices; this never breaks diameter or bipartiteness."""
    n = len(adj)
    left = [v for v in range(n) if alive[v] and color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if alive[v] and color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d:
            adj[a].add(b)
            adj[b].add(a)


def _complete(adj, color, alive, d, D, rng):
    _fill(adj, color, alive, d, D, rng)
    _saturate(adj, color, alive, d, rng)


def _export(adj, alive):
    idx = {}
    for v in range(len(adj)):
        if alive[v]:
            idx[v] = len(idx)
    edges = []
    for u in idx:
        for v in adj[u]:
            if u < v:
                edges.append((idx[u], idx[v]))
    return len(idx), edges


def _search(adj0, color0, d, D, end, rng, consider):
    """Iterated local search: delete a vertex, repair, refill; accept non-decreasing size."""
    adj = [set(s) for s in adj0]
    color = list(color0)
    alive = [True] * len(adj)
    if not _repair(adj, alive, D, rng, end):
        return
    _complete(adj, color, alive, d, D, rng)
    cur = ([set(s) for s in adj], list(color), list(alive))
    cur_cnt = sum(alive)
    best_cnt = cur_cnt
    consider(*_export(adj, alive))
    while time.monotonic() < end:
        a2 = [set(s) for s in cur[0]]
        c2 = list(cur[1])
        al2 = list(cur[2])
        alive_list = [v for v in range(len(a2)) if al2[v]]
        if not alive_list:
            break
        kills = 1 if rng.random() < 0.7 else 2
        for _ in range(kills):
            x = rng.choice(alive_list)
            if al2[x]:
                _kill(a2, al2, x)
        if not _repair(a2, al2, D, rng, end):
            break
        _complete(a2, c2, al2, d, D, rng)
        cnt = sum(al2)
        if cnt >= cur_cnt:
            cur = (a2, c2, al2)
            cur_cnt = cnt
            if cnt > best_cnt:
                best_cnt = cnt
                consider(*_export(a2, al2))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fb_n, fb_e = lib.haar_graph(d, range(d))  # K_{d,d}: valid fallback for D >= 2
    st = {"n": fb_n, "e": fb_e}

    def consider(n, e):
        if n > st["n"] and lib.is_valid(n, e, d, D):
            st["n"], st["e"] = n, e

    moore = lib.moore_bound(d, D)

    try:
        if d == 2 and D >= 2:
            m = 2 * D
            consider(m, [(i, (i + 1) % m) for i in range(m)])

        if D >= 3 and d >= 3 and st["n"] < moore:
            q = next((q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)), None)
            if q is not None:
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                adj, color = _state_from_edges(n, e)
                alive = [True] * n
                _complete(adj, color, alive, d, D, rng)
                consider(*_export(adj, alive))

        if D >= 4 and d >= 3 and st["n"] < moore:
            qs = [q for q in range(2, 9)
                  if lib.is_prime_power(q) and d <= q + 1 <= d + 2]
            if qs:
                failures = 0
                while time.monotonic() < deadline - 2.0 and failures < 20:
                    remaining = deadline - time.monotonic()
                    end = min(deadline, time.monotonic() + max(6.0, 0.6 * remaining))
                    q = rng.choice(qs)
                    base = _base_graph(q, d, rng)
                    if base is None:
                        failures += 1
                        continue
                    adj0, color0 = base
                    _search(adj0, color0, d, D, end, rng, consider)
                    if st["n"] >= moore:
                        break
    except Exception:
        pass

    n, e = st["n"], st["e"]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
