import random
import time

import lib


def _adj_lists(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
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


def _balls_radius(n, adj, r):
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
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
            thr = max(1, best_g - 1)
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng, attempts):
    """Add vertices whose neighbourhoods reach everything within D-1 of the graph."""
    if D < 2:
        return n, list(edges)
    edges = list(edges)
    adj = _adj_lists(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(attempts):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate(n, edges, d, rng):
    """Join deficient opposite-colour vertices with spare degree (only shrinks distances)."""
    edges = list(edges)
    adj = _adj_lists(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, attempts):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _remove(n, edges, gone):
    mp = [-1] * n
    k = 0
    for v in range(n):
        if v not in gone:
            mp[v] = k
            k += 1
    return k, [(mp[u], mp[v]) for u, v in edges if mp[u] >= 0 and mp[v] >= 0]


# ----------------------------------------------------------------------------
# Twin extension of PG(2,q): a point-twin attaches to the q+1 lines through
# its point, a line-twin attaches to the q+1 points on its line. A set SP of
# points (and SM of lines) can be twinned as long as every line carries at most
# s = d-q-1 twinned points and every point lies on at most s twinned lines.
# Diameter stays 3 for any such choice.
# ----------------------------------------------------------------------------

def _greedy_sets(hits, ntar, s, rng, trials, deadline):
    """Randomized greedy: items whose target lists keep every target count <= s."""
    best = []
    order = list(range(len(hits)))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cnt = [0] * ntar
        S = []
        for x in order:
            h = hits[x]
            if all(cnt[t] < s for t in h):
                S.append(x)
                for t in h:
                    cnt[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _load_ok(S, hits, ntar, s):
    cnt = [0] * ntar
    for x in S:
        for t in hits[x]:
            cnt[t] += 1
            if cnt[t] > s:
                return False
    return True


def _conic(q, idx, F):
    S = [idx[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(idx[(0, 0, 1)])
    if q % 2 == 0:
        S.append(idx[(0, 1, 0)])
    return S


def _base_graph(q, d, rng, deadline):
    """Return (n, edges, protected) for PG(2,q) plus twins using spare degree."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    s = d - q - 1
    if s < 1:
        return n2, list(edges), n2
    SP = _greedy_sets(pl, m, s, rng, 120, deadline)
    SM = _greedy_sets(lp, m, s, rng, 120, deadline)
    if s >= 2:
        pts = lib.projective_points(q)
        idx = {p: i for i, p in enumerate(pts)}
        C = _conic(q, idx, lib.GF(q))
        if len(C) > len(SP) and _load_ok(C, pl, m, s):
            SP = C
        if len(C) > len(SM) and _load_ok(C, lp, m, s):
            SM = C
    E = list(edges)
    for t, P in enumerate(SP):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    base = 2 * m + len(SP)
    for t, L in enumerate(SM):
        y = base + t
        for Q in lp[L]:
            E.append((Q, y))
    return 2 * m + len(SP) + len(SM), E, 2 * m


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.78 * time_limit
    base_end = start + 0.35 * time_limit
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fb_n, fb_e = lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2
    if D == 2 or d == 1:
        return fb_n, fb_e

    best = (fb_n, fb_e, 0)
    best_n = fb_n

    # Bases: twinned projective planes for every usable prime power q (q+1 <= d).
    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)),
                reverse=True)
    for q in qs:
        if time.monotonic() >= base_end:
            break
        n0, e0, prot = _base_graph(q, d, rng, base_end)
        n1, e1 = _grow(n0, e0, d, D, base_end, rng, 30)
        if n1 > best_n and lib.is_valid(n1, e1, d, D):
            best = (n1, e1, prot)
            best_n = n1

    # Iterated local search: delete a few twin/grown vertices, regrow, keep if not smaller.
    cur = best
    while time.monotonic() < end:
        cn, ce, prot = cur
        cand = list(range(prot, cn))
        if not cand:
            break
        r = rng.randint(1, min(3, len(cand)))
        gone = set(rng.sample(cand, r))
        n2, e2 = _remove(cn, ce, gone)
        n2, e2 = _grow(n2, e2, d, D, end, rng, 6)
        if n2 < cn:
            continue
        if not lib.is_valid(n2, e2, d, D):
            continue
        cur = (n2, e2, prot)
        if n2 > best_n:
            best = cur
            best_n = n2

    n, e, _ = best
    if not lib.is_valid(n, e, d, D):
        return fb_n, fb_e
    return n, e
