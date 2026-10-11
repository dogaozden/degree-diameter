import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C stage: a pass-through verifier hook. The search engine is Python-side for
# now; this echoes the final graph so the C path is exercised and checked.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>

int main(int argc, char **argv) {
    (void)argc;
    (void)argv;
    long n = 0, m = 0;
    if (scanf("%ld %ld", &n, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    printf("%ld %ld\n", n, m);
    for (long i = 0; i < m; i++) {
        long u, v;
        if (scanf("%ld %ld", &u, &v) != 2) break;
        printf("%ld %ld\n", u, v);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (incidence graphs of PG(2,q) and generalized quadrangles).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW: bi-Cayley (group Haar) lifts. Vertices g (side 0) and N+h (side 1) for
# g, h in a group G of order N; g ~ N + g*s for s in S, |S| = d. Left
# multiplication is an automorphism that is transitive on each side, so the
# diameter is at most D iff BFS from vertex 0 and from vertex N both reach
# everything within D. Groups are semidirect products Z_m x| Z_k.
# ----------------------------------------------------------------------------

def _group_candidates(N):
    """All (m, k, r) with m * k = N giving a semidirect product Z_m x| Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group_tables(m, k, r):
    """Order N, multiplication table and inverse table of Z_m x| Z_k (identity is index 0)."""
    N, mul, inv = lib.semidirect_group(m, k, r)
    mt = [[mul(x, y) for y in range(N)] for x in range(N)]
    iv = [inv(x) for x in range(N)]
    return N, mt, iv


def _lift_cost(N, mt, iv, S, D):
    """Number of (source, target) pairs at distance > D from the two base vertices (0 and N)."""
    Si = [iv[s] for s in S]
    adj = [None] * (2 * N)
    for g in range(N):
        row = mt[g]
        adj[g] = [N + row[s] for s in S]
    for h in range(N):
        row = mt[h]
        adj[N + h] = [row[si] for si in Si]
    cost = 0
    for src in (0, N):
        dist = [-1] * (2 * N)
        dist[src] = 0
        frontier = [src]
        for depth in range(1, D + 1):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if dist[v] < 0:
                        dist[v] = depth
                        nxt.append(v)
            frontier = nxt
            if not frontier:
                break
        cost += dist.count(-1)
    return cost


def _climb(N, mt, iv, d, D, rng, iters, deadline):
    """Hill-climb a d-subset S of the group so the bi-Cayley lift has diameter <= D."""
    S = rng.sample(range(N), d)
    cur = _lift_cost(N, mt, iv, S, D)
    it = 0
    while cur and it < iters:
        it += 1
        if (it & 15) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        s = rng.randrange(N)
        if s in S:
            continue
        T = list(S)
        T[i] = s
        c = _lift_cost(N, mt, iv, T, D)
        if c <= cur:
            S, cur = T, c
    return S if cur == 0 else None


def _group_phase(d, D, lo, hi, deadline, rng, consider):
    """For each order N in [lo, hi] (ascending), try a few groups; keep any valid lift."""
    for N in range(lo, hi + 1):
        if time.monotonic() >= deadline:
            return
        if N < d:
            continue
        cands = _group_candidates(N)
        rng.shuffle(cands)
        for m, k, r in cands[:4]:
            if time.monotonic() >= deadline:
                return
            _, mt, iv = _group_tables(m, k, r)
            S = _climb(N, mt, iv, d, D, rng, 400, deadline)
            if S is not None:
                e2 = [(g, N + mt[g][s]) for g in range(N) for s in S]
                consider(2 * N, e2)
                break


# ----------------------------------------------------------------------------
# Shared graph helpers (from the parent).
# ----------------------------------------------------------------------------

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
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
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


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
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


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
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
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, attempts=200):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Twin duplication.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add twins in random order while neighbours have spare degree."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    return n, e


# ----------------------------------------------------------------------------
# Random voltage lifts of small d-regular bipartite base multigraphs.
# ----------------------------------------------------------------------------

def _random_lift(k, m, d, rng):
    """Random Z_m lift of a d-regular bipartite multigraph on k + k base vertices."""
    darts = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            darts.append((i, k + perm[i], rng.randrange(m)))
    return lib.voltage_lift(2 * k, darts, m)


def _lift_search(d, D, deadline, rng, best_n, consider):
    """Search random voltage lifts slightly above best_n, repair them, then grow."""
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        if best_n >= moore:
            return
        k = rng.choice((1, 1, 2, 3))
        target = min(moore, best_n + rng.randint(1, 12))
        m = -(-target // (2 * k))
        if 2 * k * m > moore:
            m = moore // (2 * k)
        if m < 2 or 2 * k * m <= best_n:
            continue
        n, e = _random_lift(k, m, d, rng)
        adj = _to_sets(n, e)
        color = [0 if v < k * m else 1 for v in range(n)]
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(n) for v in adj[u] if u < v]
        consider(n, e3)
        n4, e4 = _grow(n, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n = n4


# ----------------------------------------------------------------------------
# Annealing, large-neighbourhood search and repair (from the parent).
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
    """Append a vertex on the opposite side of `side`, joined to a greedy cover of `side`."""
    n = len(adj)
    ball = _balls_radius(n, adj, D - 1)
    covered = 0
    chosen = []
    cands = [s for s in range(n) if color[s] == side]
    for _ in range(d):
        best_s, best_g = None, -1.0
        for s in cands:
            if s in chosen:
                continue
            g = (ball[s] & ~covered).bit_count() + 0.5 * rng.random()
            if g > best_g:
                best_s, best_g = s, g
        if best_s is None:
            break
        chosen.append(best_s)
        covered |= ball[best_s]
    v = n
    adj.append(set())
    color.append(1 - side)
    for s in chosen:
        if len(adj[s]) >= d:
            t = rng.choice(tuple(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return v


def _fill(adj, color, d, rng):
    """Add cross-side edges between deficient vertices (only helps the diameter)."""
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    """Bipartite double-edge switches (degrees unchanged) minimising bad pairs. True if cost reaches 0."""
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 3))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


def _repair(d, D, n, edges, deadline, rng, consider):
    """Repeatedly try to add one vertex to the current valid graph, repairing with annealing."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        side = rng.randrange(2)
        _add_vertex(adj, color, d, D, side, rng)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(u, v) for u in range(m) for v in adj[u] if u < v]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


# ----------------------------------------------------------------------------
# Pipeline from the parent, run on whatever the group phase left behind.
# ----------------------------------------------------------------------------

def _pipeline(d, D, rng, t_end, consider, state, struct):
    """Structured growth, twin trials, voltage lifts, LNS, then repair, until t_end."""
    t0 = time.monotonic()
    span = max(0.0, t_end - t0)

    def at(f):
        return t0 + f * span

    base_n, base_e = state["n"], list(state["e"])
    if struct is not None:
        n0, e0 = struct
        n1, e1 = _grow(n0, e0, d, D, at(0.15), rng)
        consider(n1, e1)
        if lib.is_valid(n1, e1, d, D):
            base_n, base_e = n1, list(e1)
        else:
            base_n, base_e = n0, list(e0)

    trial_end = at(0.35)
    while time.monotonic() < trial_end:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    if time.monotonic() < at(0.5):
        _lift_search(d, D, at(0.5), rng, state["n"], consider)

    if time.monotonic() < at(0.8):
        _lns(state["n"], list(state["e"]), d, D, at(0.8), rng, consider)

    if time.monotonic() < t_end:
        _repair(d, D, state["n"], list(state["e"]), t_end, rng, consider)


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    state = {"n": fallback[0], "e": list(fallback[1])}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"], state["e"] = n, list(e)

    struct = None
    try:
        # Structured base: GQ for D >= 4, projective plane for D = 3.
        if D >= 3:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
            if base is not None:
                struct = base
                consider(base[0], base[1])

        # NEW construction: bi-Cayley lifts over semidirect products, searched
        # for diameter D at orders above the current best.
        if D >= 2:
            moore = lib.moore_bound(d, D)
            hi_all = moore // 2
            lo = max(state["n"] // 2 + 1, hi_all - 90, 2)
            hi = min(hi_all, lo + 120, 600)
            if lo <= hi:
                _group_phase(d, D, lo, hi, t_start + 0.5 * time_limit, rng, consider)
    except Exception:
        pass

    try:
        if D >= 2:
            _pipeline(d, D, rng, t_start + 0.8 * time_limit, consider, state, struct)
    except Exception:
        pass

    n, e = state["n"], list(state["e"])
    if not lib.is_valid(n, e, d, D):
        return fallback[0], list(fallback[1])

    # Pass the final graph through the C stage; accept only an exact, valid echo.
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, 1], stdin_graph=(n, e), timeout=20.0)
        n2, e2 = lib.parse_graph_text(out)
        if n2 == n and len(e2) == len(e) and lib.is_valid(n2, e2, d, D):
            return n2, e2
    except Exception:
        pass
    return n, e
