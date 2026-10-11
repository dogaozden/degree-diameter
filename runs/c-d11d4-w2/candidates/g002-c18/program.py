import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
int main(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 1;
        printf("%d %d\n", u, v);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are the points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree q + 1,
    diameter 4, order 2(q+1)(q^2+1).
    """
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Growth moves from the previous generation. Each keeps diameter <= D and
# bipartiteness: twins, cover vertices and extra edges never increase distances.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices while every neighbour of the original vertex has spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


def _remove_twins(n, edges, frac, rng):
    """Delete a random fraction of redundant twins (same neighbourhood); diameter is preserved."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    classes = {}
    for v in range(n):
        if adj[v]:
            classes.setdefault(frozenset(adj[v]), []).append(v)
    cands = []
    for grp in classes.values():
        if len(grp) >= 2:
            cands.extend(grp[1:])
    if not cands:
        return n, list(edges)
    k = max(1, int(frac * len(cands)))
    drop = set(rng.sample(cands, min(k, len(cands))))
    keep = [v for v in range(n) if v not in drop]
    idx = {v: i for i, v in enumerate(keep)}
    new_e = [(idx[u], idx[v]) for u, v in edges if u not in drop and v not in drop]
    return len(keep), new_e


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy cover of `full` by at most d candidates; returns the chosen list or None."""
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within distance D."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
            for attempt in range(40):
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


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
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


def _grow(n, edges, d, D, deadline, rng):
    """Cover extension first, then edge saturation with the spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth and cover growth until neither adds a vertex."""
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# New family: add ONE vertex at a time to a valid graph, then repair the whole
# graph by simulated annealing over degree-preserving or degree-bounded rewires.
# The cost is the number of vertex pairs at distance > D. Every move keeps
# max degree <= d and bipartiteness, so a cost-0 state is a valid graph with
# one more vertex.
# ----------------------------------------------------------------------------

def _bad(N, adjs, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = reach[v]
            for u in adjs[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _apply(adjs, ops):
    for op, u, v in ops:
        if op == 0:
            adjs[u].discard(v)
            adjs[v].discard(u)
        else:
            adjs[u].add(v)
            adjs[v].add(u)


def _revert(adjs, ops):
    for op, u, v in reversed(ops):
        if op == 0:
            adjs[u].add(v)
            adjs[v].add(u)
        else:
            adjs[u].discard(v)
            adjs[v].discard(u)


def _repair(N, adjs, color, d, D, deadline, rng):
    """Anneal until the cost is 0 (returns True) or the deadline passes (returns False)."""
    cost = _bad(N, adjs, D)
    t_begin = time.monotonic()
    span = max(1e-3, deadline - t_begin)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return False
        T = 1.0 * (1.0 - (now - t_begin) / span) + 0.05
        ops = []
        mv = rng.random()
        if mv < 0.1:
            # Add an edge between two spare vertices: never increases the cost.
            spare = [x for x in range(N) if len(adjs[x]) < d]
            if spare:
                a = rng.choice(spare)
                cands = [x for x in spare if color[x] != color[a] and x not in adjs[a]]
                if cands:
                    ops = [(1, a, rng.choice(cands))]
        elif mv < 0.6:
            # Rewire one end of an edge to a spare opposite-side vertex.
            a = rng.randrange(N)
            if adjs[a]:
                b = rng.choice(list(adjs[a]))
                for _ in range(15):
                    c = rng.randrange(N)
                    if color[c] != color[a] and c not in adjs[a] and len(adjs[c]) < d:
                        ops = [(0, a, b), (1, a, c)]
                        break
        else:
            # Degree-preserving double edge swap.
            a = rng.randrange(N)
            same = [x for x in range(N) if color[x] == color[a] and x != a and adjs[x]]
            if adjs[a] and same:
                a2 = rng.choice(same)
                b = rng.choice(list(adjs[a]))
                b2 = rng.choice(list(adjs[a2]))
                if b2 not in adjs[a] and b not in adjs[a2] and b != b2:
                    ops = [(0, a, b), (0, a2, b2), (1, a, b2), (1, a2, b)]
        if not ops:
            continue
        _apply(adjs, ops)
        new = _bad(N, adjs, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            if cost == 0:
                return True
        else:
            _revert(adjs, ops)
    return True


def _add_one(N, adjs, d, D, deadline, rng):
    """Try to add one vertex to a copy of the graph; return the new adjacency sets or None."""
    adjl = [list(s) for s in adjs]
    color = _bipartition(N, adjl)
    c = rng.randrange(2)
    ball = _balls_radius(N, adjl, D - 1)
    full = (1 << N) - 1
    cands = [s for s in range(N) if color[s] == 1 - c]
    chosen = None
    for att in range(20):
        chosen = _greedy_cover(cands, ball, full, d, rng, att > 0)
        if chosen:
            break
    if not chosen:
        chosen = rng.sample(cands, min(d, len(cands)))
    new = [set(s) for s in adjs]
    v = N
    new.append(set())
    color.append(c)
    for s in chosen:
        if len(new[s]) >= d:
            x = rng.choice(list(new[s]))
            new[s].discard(x)
            new[x].discard(s)
        new[s].add(v)
        new[v].add(s)
    if _repair(N + 1, new, color, d, D, deadline, rng):
        return new
    return None


def _anneal_grow(n, edges, d, D, deadline, rng):
    """Repeatedly add one vertex and repair; return the largest valid (n, edges) reached."""
    adjs = [set() for _ in range(n)]
    for u, v in edges:
        adjs[u].add(v)
        adjs[v].add(u)
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        now = time.monotonic()
        attempt_end = min(deadline, now + 0.35 * (deadline - now) + 2.0)
        res = _add_one(cur_n, adjs, d, D, attempt_end, rng)
        if res is None:
            if time.monotonic() >= deadline:
                break
            continue
        adjs = res
        cur_n += 1
        cur_e = [(u, v) for u in range(cur_n) for v in adjs[u] if u < v]
    return cur_n, cur_e


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, list(e))
            best_n = n

    base = None
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            base = pg
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if base is None or gq[0] > base[0]:
                base = gq

    # Phase 1 (until 45%): grow the best base by twin/cover/saturation passes.
    t1 = t0 + 0.45 * time_limit
    if base is not None:
        cur = None
        while time.monotonic() < t1:
            if cur is None or rng.random() < 0.25:
                sn, se = base
            else:
                sn, se = _remove_twins(cur[0], cur[1], rng.uniform(0.05, 0.3), rng)
                se = _saturate_edges(sn, se, d, rng)
            pn, pe = _pipeline(sn, se, d, D, t1, rng)
            consider(pn, pe)
            if cur is None or pn >= cur[0]:
                cur = (pn, pe)

    # Phase 2 (until 88%): add vertices one at a time with annealing repair,
    # starting from the best valid graph found so far.
    t2 = t0 + 0.88 * time_limit
    if D >= 3 and time.monotonic() < t2:
        bn, be = best
        gn, ge = _anneal_grow(bn, be, d, D, t2, rng)
        consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
