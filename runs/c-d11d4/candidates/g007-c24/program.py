import itertools
import math
import random
import time

import numpy as np

import lib


# The C engine is kept as a small, valid pass-through. The search is in Python.
C_SOURCE = r"""
#include <stdio.h>
int main(void) {
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
# Base constructions.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q), order 2(q+1)(q^2+1)."""
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
# Twins: a twin of x (same side, same neighbourhood) keeps all distances and
# needs one spare degree on each neighbour of x.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
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
    """Delete a random fraction of redundant twins; this preserves all remaining distances."""
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


# ----------------------------------------------------------------------------
# Cover helpers. A new vertex on side c is at distance <= D from everything iff
# its neighbourhood S covers all vertices within distance D-1 of some s in S.
# ----------------------------------------------------------------------------

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
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _ball_rows(ball, idx, n):
    """float32 0/1 matrix: row r is the ball of idx[r] over n vertices."""
    nb = (n + 7) // 8
    out = np.zeros((len(idx), n), dtype=np.float32)
    for r, s in enumerate(idx):
        arr = np.frombuffer(ball[s].to_bytes(nb, "little"), dtype=np.uint8)
        out[r] = np.unpackbits(arr, bitorder="little")[:n]
    return out


def _weighted_cover(sub, cands, n, d, rng, randomize):
    """Rarity-weighted greedy cover: uncovered vertices that few candidates reach get large weight."""
    k = sub.shape[0]
    uncovered = np.ones(n, dtype=np.float32)
    avail_b = np.ones(k, dtype=bool)
    chosen = []
    while uncovered.sum() > 0:
        if len(chosen) >= d or not avail_b.any():
            return None
        avail = avail_b.astype(np.float32)
        cnt = avail @ sub
        if np.any((uncovered > 0) & (cnt < 0.5)):
            return None
        w = np.where(uncovered > 0, 1.0 / np.maximum(cnt, 1.0), 0.0).astype(np.float32)
        gain = sub @ w
        gain[~avail_b] = -1.0
        best = float(gain.max())
        if best <= 0:
            return None
        if randomize:
            thr = best * (0.9 if rng.random() < 0.3 else 1.0)
            opts = np.flatnonzero((gain >= thr) & avail_b)
            i = int(opts[rng.randrange(len(opts))])
        else:
            i = int(np.argmax(gain))
        chosen.append(cands[i])
        avail_b[i] = False
        uncovered[sub[i] > 0] = 0.0
    return chosen


def _weighted_cover_search(cands, ball, n, d, rng, tries, deadline):
    sub = _ball_rows([ball[s] for s in cands], list(range(len(cands))), n)
    for t in range(tries):
        if time.monotonic() >= deadline:
            break
        ch = _weighted_cover(sub, cands, n, d, rng, t > 0)
        if ch:
            return ch
    return None


def _find_cover(cands, ball, n, full, d, rng, deadline):
    """Greedy covers first (cheap), then rarity-weighted covers."""
    for attempt in range(20):
        if time.monotonic() >= deadline:
            return None
        ch = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
        if ch:
            return ch
    if time.monotonic() < deadline:
        return _weighted_cover_search(cands, ball, n, d, rng, 10, deadline)
    return None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily append whole vertices whose neighbourhoods cover every vertex (spare degree only)."""
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
            chosen = _find_cover(cands, ball, n, full, d, rng, deadline)
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
    """Join deficient opposite-side vertices with spare degree (adds edges only)."""
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


def _grow(n, edges, d, D, deadline, rng):
    """Cover extension, then saturation with the leftover spare degree, repeated."""
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
    """Alternate twin growth and cover growth until nothing changes. Output is valid if input is."""
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


def _gq_iterate(gq, d, D, end, rng, consider):
    """Iterated regrowth. Sources: fresh W(q), a twin-thinned copy of the best graph,
    or a twin-thinned copy of the current chain. Returns the best (n, edges) seen."""
    cur = None
    top = gq
    while time.monotonic() < end:
        r = rng.random()
        if cur is None or r < 0.2:
            src = gq
        elif r < 0.55:
            src = _remove_twins(top[0], top[1], rng.choice((0.1, 0.2, 0.3)), rng)
        else:
            src = _remove_twins(cur[0], cur[1], 0.15, rng)
        pn, pe = _pipeline(src[0], src[1], d, D, end, rng)
        consider(pn, pe)
        if pn > top[0]:
            top = (pn, pe)
        if cur is None or pn >= cur[0]:
            cur = (pn, pe)
    return top


# ----------------------------------------------------------------------------
# Rewire-then-extend: delete a few random edges to free degree, try to attach a
# covering vertex, keep the move only if the full graph still has diameter <= D.
# ----------------------------------------------------------------------------

def _edges_of(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _rewire_extend(n, edges, d, D, deadline, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n, [list(s) for s in adj])
    while time.monotonic() < deadline:
        c = rng.randrange(2)
        k = rng.choice((0, 1, 1, 2, 3))
        dropped = []
        for _ in range(k):
            s = rng.randrange(n)
            if not adj[s]:
                continue
            t = rng.choice(sorted(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
            dropped.append((s, t))
        adj_l = [list(x) for x in adj]
        ball = _balls_radius(n, adj_l, D - 1)
        full = (1 << n) - 1
        cands = [s for s in range(n) if color[s] == 1 - c and len(adj[s]) < d]
        chosen = None
        if cands:
            chosen = _find_cover(cands, ball, n, full, d, rng, deadline)
        ok = False
        if chosen:
            v = n
            for s in chosen:
                adj[s].add(v)
            adj.append(set(chosen))
            n_new = n + 1
            if lib.bad_pairs(n_new, _edges_of(n_new, adj), D) == 0:
                n = n_new
                color.append(c)
                ok = True
            else:
                for s in chosen:
                    adj[s].discard(v)
                adj.pop()
        if not ok:
            for s, t in dropped:
                adj[s].add(t)
                adj[t].add(s)
    return n, _edges_of(n, adj)


# ----------------------------------------------------------------------------
# Voltage lifts: cyclic, Haar, and semidirect (non-cyclic) groups.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _group_search(d, D, k, G, rng, iters, deadline):
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        if order < 2:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


def _search_haar(d, D, m, rng, deadline, iters):
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _search_lift(d, D, k, m, rng, iters, deadline):
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        touched = [rng.randrange(len(darts))]
        if rng.random() < 0.2:
            touched.append(rng.randrange(len(darts)))
        olds = [(j, darts[j][2]) for j in touched]
        for j in touched:
            if m > 1:
                darts[j][2] = (darts[j][2] + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            for j, old in olds:
                darts[j][2] = old
    if c == 0:
        return n, e
    return None


def _lift_loop(d, D, best_n, deadline, rng, consider):
    group_p = 0.3
    haar_p = 0.2 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0
    cur_best = best_n
    while time.monotonic() < deadline:
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = cur_best // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, deadline)
            if res is not None:
                consider(res[0], res[1])
                cur_best = max(cur_best, res[0])
                st["G"] = G + st["step"]
                st["step"] = min(st["step"] * 2, max(1, G // 10))
                st["miss"] = 0
            else:
                st["G"] = G
                st["miss"] += 1
                if st["miss"] >= 3:
                    st["step"] = 1
                    st["miss"] = 0
                    st["G"] = floor
        elif rng.random() < haar_p and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                cur_best = max(cur_best, n)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice(base_sizes)
            m = max(ladder[k], cur_best // (2 * k) + 1, 2)
            res = _search_lift(d, D, k, m, rng, 250, deadline)
            if res is not None:
                consider(res[0], res[1])
                cur_best = max(cur_best, res[0])
                ladder[k] = m + 1
            else:
                ladder[k] = m


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.87 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2 and optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    bound = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if best_n >= bound:
        return best

    if D == 3:
        # Araujo-Pardo and Lopez record for d = q + 2 with q a prime power.
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass
        # Projective planes for the two largest prime powers q with q + 1 <= d, grown in time slices.
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
        for i, q in enumerate(qs):
            if best_n >= bound or time.monotonic() >= deadline:
                break
            pg_n, pg_e = lib.projective_plane_incidence(q)
            consider(pg_n, pg_e)
            slice_end = start + 0.4 * time_limit * (i + 1) / len(qs)
            pn, pe = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
            consider(pn, pe)
        if best_n < bound and time.monotonic() < deadline:
            rn, re_ = _rewire_extend(best_n, best[1], d, D, start + 0.6 * time_limit, rng)
            consider(rn, re_)
        if best_n < bound and time.monotonic() < deadline:
            _lift_loop(d, D, best_n, deadline, rng, consider)

    elif D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            # Phase 1: iterated regrowth from W(q), twin-thinned best, and current chain.
            top = _gq_iterate(gq, d, D, start + 0.45 * time_limit, rng, consider)
            consider(top[0], top[1])
            # Phase 2: rewire-then-extend from the best graph.
            if best_n < bound and time.monotonic() < start + 0.8 * time_limit:
                rn, re_ = _rewire_extend(best_n, best[1], d, D, start + 0.8 * time_limit, rng)
                consider(rn, re_)
            # Phase 3: final growth pass on the best graph.
            if time.monotonic() < deadline:
                pn, pe = _pipeline(best_n, best[1], d, D, deadline, rng)
                consider(pn, pe)
        if best_n < bound and time.monotonic() < deadline:
            _lift_loop(d, D, best_n, deadline, rng, consider)

    else:
        # D == 2 with bound not reached cannot happen (K_{d,d} is optimal), but keep a safe path.
        _lift_loop(d, D, best_n, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
