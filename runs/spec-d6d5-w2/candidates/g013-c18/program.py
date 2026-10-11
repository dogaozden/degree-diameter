import itertools
import math
import random
import time

import numpy as np

import lib


_POP = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


# ----------------------------------------------------------------------------
# Base families: projective plane (D = 3 sanity), generalized quadrangle W(q)
# (diameter 4, the base for the new lift family), and cover/saturation growth.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _gq_q(d):
    """Largest prime power q <= min(d - 1, 9), q >= 2, or None."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


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
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
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


def _extend_cover(n, edges, d, D, deadline, rng, randomize=False):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
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
            for attempt in range(60):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, randomize or attempt > 0)
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
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
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


def _grow(n, edges, d, D, deadline, rng, randomize=False):
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, randomize)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Diameter repair by vertex deletion.
# ----------------------------------------------------------------------------

def _compact(n, edges, keep):
    """Relabel the kept vertices to 0..m-1 and keep only edges between them."""
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges) or None."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
        ball = _balls_radius(cur_n, adj, D)
        bad = [cur_n - b.bit_count() for b in ball]
        if not any(bad):
            return cur_n, cur_e
        bad_v = [v for v in range(cur_n) if bad[v] > 0]
        rng.shuffle(bad_v)
        bad_v.sort(key=lambda v: -bad[v])
        batch = max(1, len(bad_v) // 12)
        dead = set(bad_v[:batch])
        keep = [v not in dead for v in range(cur_n)]
        cur_n, cur_e = _compact(cur_n, cur_e, keep)
    return None


# ----------------------------------------------------------------------------
# NEW FAMILY: Z_m voltage lifts of the generalized quadrangle incidence graph.
#
# Base: bipartite W(q) incidence graph (diameter 4, (q+1)-regular, 2(q+1)(q^2+1)
# vertices). Lift by Z_m: base vertex x becomes m copies (x, g); base edge
# e = (u, v) with voltage a_e joins (u, g) to (v, g + a_e). The lift stays
# bipartite and simple, keeps the degree, and Z_m acts by translation, so
# checking distances from the copies (x, 0) suffices.
#
# The search is fully vectorised: reach sets are packed bitsets over all
# N = base_n * m vertices, updated by numpy OR-reductions, so one evaluation
# costs a few milliseconds and annealing runs thousands of moves.
# Lifts that stall at a few bad pairs are repaired by vertex deletion followed
# by edge saturation (which only shortens distances).
# ----------------------------------------------------------------------------

def _lift_struct(base_n, base_edges, m, D):
    """Precomputed index arrays for Z_m lifts of a base graph."""
    src, dst, eid, sign, slot = [], [], [], [], []
    deg = [0] * base_n
    for e, (u, v) in enumerate(base_edges):
        for a, b, s in ((u, v, 1), (v, u, -1)):
            src.append(a)
            dst.append(b)
            eid.append(e)
            sign.append(s)
            slot.append(deg[a])
            deg[a] += 1
    k = max(deg)
    N = base_n * m
    idx = np.arange(N, dtype=np.int64)
    B = (N + 7) // 8
    init = np.zeros((N, B), dtype=np.uint8)
    init[idx, idx >> 3] = np.left_shift(1, idx & 7).astype(np.uint8)
    return {
        "N": N, "k": k, "E": len(base_edges), "m": m, "D": D,
        "src": np.array(src, dtype=np.int64),
        "dst": np.array(dst, dtype=np.int64),
        "eid": np.array(eid, dtype=np.int64),
        "sign": np.array(sign, dtype=np.int64),
        "slot": np.array(slot, dtype=np.int64),
        "gs": np.arange(m, dtype=np.int64),
        "adj0": np.repeat(idx[:, None], k, axis=1),
        "init": init,
        "reps": np.arange(0, N, m, dtype=np.int64),
    }


def _lift_adj(st, V):
    """Adjacency array (N, k) of the lift with voltages V (padded with self-loops, harmless for reach)."""
    m = st["m"]
    gs = st["gs"]
    shift = (st["sign"] * V[st["eid"]]) % m
    tgt = st["dst"][:, None] * m + (gs[None, :] + shift[:, None]) % m
    rows = st["src"][:, None] * m + gs[None, :]
    cols = np.broadcast_to(st["slot"][:, None], rows.shape)
    adj = st["adj0"].copy()
    adj[rows, cols] = tgt
    return adj


def _lift_bad(st, adj):
    """Per-vertex count of vertices NOT reached within D steps."""
    reach = st["init"].copy()
    for _ in range(st["D"]):
        reach = np.bitwise_or.reduce(reach[adj], axis=1) | reach
    cnt = _POP[reach].sum(axis=1)
    return st["N"] - cnt


def _lift_cost(st, V):
    return int(_lift_bad(st, _lift_adj(st, V))[st["reps"]].sum())


def _anneal_lift(st, rng, deadline, V0=None, max_evals=10 ** 9):
    """Simulated annealing over the voltages. Returns (best_cost, best_V)."""
    E, m = st["E"], st["m"]
    if V0 is None:
        V = np.array([rng.randrange(m) for _ in range(E)], dtype=np.int64)
    else:
        V = V0.copy()
    cur = _lift_cost(st, V)
    best_c, best_V = cur, V.copy()
    T = 1.5
    evals = 0
    while cur > 0 and evals < max_evals and time.monotonic() < deadline:
        e = rng.randrange(E)
        old = int(V[e])
        new = rng.randrange(m)
        if new == old:
            continue
        V[e] = new
        evals += 1
        c2 = _lift_cost(st, V)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
            if cur < best_c:
                best_c, best_V = cur, V.copy()
        else:
            V[e] = old
        T = max(0.3, T * 0.9995)
    return best_c, best_V


def _lift_edges(base_edges, V, m):
    E = []
    for e, (u, v) in enumerate(base_edges):
        a = int(V[e])
        for g in range(m):
            E.append((u * m + g, v * m + (g + a) % m))
    return E


def _lift_phase(base_n, base_edges, d, D, deadline, rng, consider):
    """Anneal Z_m lifts of the base graph; accept zero-cost lifts, repair near misses."""
    ms = [m for m in (3, 4, 5) if base_n * m <= 1600]
    if not ms:
        return
    elite = {}
    while time.monotonic() < deadline:
        if rng.random() < 0.6:
            m = ms[0]
        else:
            m = rng.choice(ms)
        st = _lift_struct(base_n, base_edges, m, D)

        V0 = None
        if m in elite and rng.random() < 0.5:
            V0 = elite[m][1].copy()
            for _ in range(rng.randint(1, 4)):
                V0[rng.randrange(len(V0))] = rng.randrange(m)

        budget = min(deadline, time.monotonic() + 8.0)
        c, V = _anneal_lift(st, rng, budget, V0)
        n = base_n * m
        edges = _lift_edges(base_edges, V, m)

        if c == 0:
            consider(n, edges)
            continue

        if m not in elite or c < elite[m][0]:
            elite[m] = (c, V)

        # Near miss: delete the worst vertices until diameter <= D, then saturate.
        if rng.random() < 0.5 and time.monotonic() < deadline:
            rep_deadline = min(deadline, time.monotonic() + 5.0)
            rep = _repair(n, edges, D, rep_deadline, rng)
            if rep is not None:
                rn, re = rep
                consider(rn, re)
                se = _saturate_edges(rn, re, d, rng)
                consider(rn, se)


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    try:
        if D >= 3 and D < 5:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.1 * time_limit, rng)
                consider(n2, e2)
                restart_deadline = start + 0.15 * time_limit
                grow_rng = random.Random(seed * 104729 + d * 31 + D)
                while time.monotonic() < restart_deadline:
                    n4, e4 = _grow(pg[0], pg[1], d, D, restart_deadline, grow_rng, randomize=True)
                    if n4 > best_n:
                        consider(n4, e4)
    except Exception:
        pass

    gq_base = None
    try:
        if D >= 4:
            q = _gq_q(d)
            if q is not None:
                bn, be = _gq_w(q)
                consider(bn, be)
                gq_base = (bn, be)
                if D == 4:
                    n2, e2 = _grow(bn, be, d, D, start + 0.3 * time_limit, rng)
                    consider(n2, e2)
                else:
                    n2, e2 = _grow(bn, be, d, D, start + 0.05 * time_limit, rng)
                    consider(n2, e2)
    except Exception:
        pass

    # Bold change for D >= 5: voltage lifts of the generalized quadrangle
    # incidence graph (diameter 4), repaired by deletion when near-miss.
    if D >= 5 and d >= 3 and gq_base is not None:
        lift_rng = random.Random(seed * 1000003 + d * 131 + D)
        try:
            _lift_phase(gq_base[0], gq_base[1], d, D, deadline, lift_rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
