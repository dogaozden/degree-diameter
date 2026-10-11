import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


_GQ_CACHE = {}


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q). Degree q+1, diameter 4."""
    if q in _GQ_CACHE:
        return _GQ_CACHE[q]
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
    res = (2 * P, edges)
    _GQ_CACHE[q] = res
    return res


# ----------------------------------------------------------------------------
# Growth tools. Every step keeps diameter <= D and bipartiteness.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices (same side, same neighbourhood) while neighbours have spare degree."""
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
    """Delete a random fraction of redundant twins; the diameter is preserved."""
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
    """Greedy set cover of `full` by at most d candidate vertices."""
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
    """float32 membership matrix: row r is the ball of idx[r] as a 0/1 vector over n vertices."""
    nb = (n + 7) // 8
    out = np.zeros((len(idx), n), dtype=np.float32)
    for r, s in enumerate(idx):
        arr = np.frombuffer(ball[s].to_bytes(nb, "little"), dtype=np.uint8)
        out[r] = np.unpackbits(arr, bitorder="little")[:n]
    return out


def _weighted_cover(sub, cands, n, d, rng, randomize):
    """Rarity-weighted greedy cover of all n vertices by at most d candidate rows of sub."""
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
    """Try several weighted covers (first deterministic, then randomised)."""
    sub = _ball_rows(ball, cands, n)
    for t in range(tries):
        if time.monotonic() >= deadline:
            break
        ch = _weighted_cover(sub, cands, n, d, rng, t > 0)
        if ch:
            return ch
    return None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods cover all current vertices within radius D-1."""
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
            for attempt in range(40):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if not chosen and time.monotonic() < deadline:
                chosen = _weighted_cover_search(cands, ball, n, d, rng, 15, deadline)
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


def _extend_pairs(n, edges, d, D, deadline, rng):
    """Greedily add adjacent pairs (v on side 0, w on side 1) whose neighbourhoods cover old vertices."""
    if D < 3 or d < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    fails = 0
    while fails < 3 and time.monotonic() < deadline:
        r1 = _balls_radius(n, adj, D - 1)
        r2 = _balls_radius(n, adj, D - 2)
        full = (1 << n) - 1
        Uv, Uw = full, full
        Sv, Sw, used = [], [], set()
        pool1 = [s for s in range(n) if color[s] == 1 and deg[s] < d]
        pool0 = [s for s in range(n) if color[s] == 0 and deg[s] < d]
        ok = True
        while Uv or Uw:
            if time.monotonic() >= deadline:
                ok = False
                break
            best_key, pick, pside = -1.0, None, None
            if len(Sv) < d - 1:
                for s in pool1:
                    if s in used:
                        continue
                    sc = (r1[s] & Uv).bit_count() + (r2[s] & Uw).bit_count()
                    key = sc + 0.99 * rng.random()
                    if sc > 0 and key > best_key:
                        best_key, pick, pside = key, s, 1
            if len(Sw) < d - 1:
                for t in pool0:
                    if t in used:
                        continue
                    sc = (r1[t] & Uw).bit_count() + (r2[t] & Uv).bit_count()
                    key = sc + 0.99 * rng.random()
                    if sc > 0 and key > best_key:
                        best_key, pick, pside = key, t, 0
            if pick is None:
                ok = False
                break
            used.add(pick)
            if pside == 1:
                Sv.append(pick)
                Uv &= ~r1[pick]
                Uw &= ~r2[pick]
            else:
                Sw.append(pick)
                Uw &= ~r1[pick]
                Uv &= ~r2[pick]
        if not ok:
            fails += 1
            continue
        fails = 0
        v, w = n, n + 1
        n += 2
        color.extend([0, 1])
        adj.extend([[], []])
        deg.extend([0, 0])
        for s in Sv:
            edges.append((s, v))
            adj[s].append(v)
            adj[v].append(s)
            deg[s] += 1
            deg[v] += 1
        for t in Sw:
            edges.append((t, w))
            adj[t].append(w)
            adj[w].append(t)
            deg[t] += 1
            deg[w] += 1
        edges.append((v, w))
        adj[v].append(w)
        adj[w].append(v)
        deg[v] += 1
        deg[w] += 1
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
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return n, edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then pair vertices, then saturate edges, until stable."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        n3, e3 = _extend_pairs(n2, e2, d, D, deadline, rng)
        grew = n3 != cur_n
        cur_n = n3
        cur_n, cur_e = _saturate_edges(cur_n, e3, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth and cover/pair growth until no vertex is added."""
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
# NEW family for D >= 4: exact-degree-ish quadrangle bases with perturb-and-regrow.
# Every prime power q with q + 1 <= d (q <= 9 for construction speed) gives a base
# W(q) of degree q+1. Smaller q leaves more spare degree, so growth is less constrained.
# Bases are visited round-robin in chunks; each visit either regrows the base or a
# perturbed copy (twin removal, then saturation) of that base's best result so far.
# ----------------------------------------------------------------------------

def _gq_growth(d, D, qs, rng, deadline, consider, chunk):
    """Round-robin perturb-and-regrow over several W(q) bases until deadline."""
    state = {q: {"base": None, "cur": None} for q in set(qs)}
    while time.monotonic() < deadline:
        for q in qs:
            if time.monotonic() >= deadline:
                return
            st = state[q]
            if st["base"] is None:
                st["base"] = _gq_w(q)
                consider(st["base"][0], st["base"][1])
            if st["cur"] is None or rng.random() < 0.2:
                sn, se = st["base"]
            else:
                sn, se = _remove_twins(st["cur"][0], st["cur"][1], rng.uniform(0.05, 0.3), rng)
                se = _saturate_edges(sn, se, d, rng)
            end = min(deadline, time.monotonic() + chunk)
            pn, pe = _pipeline(sn, se, d, D, end, rng)
            consider(pn, pe)
            if st["cur"] is None or pn >= st["cur"][0]:
                st["cur"] = (pn, pe)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
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
            best = (n, e)
            best_n = n

    # D = 3: projective planes grown by the twin + cover + pair pipeline.
    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            t0 = time.monotonic()
            ext_deadline = start + 0.5 * time_limit
            span = max(0.0, ext_deadline - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    # D >= 4: new bold family. Smaller and larger generalized-quadrangle bases compete,
    # with the largest-degree-fitting bases visited most often.
    if D >= 4:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        qs = [q for q in range(9, 1, -1) if q + 1 <= d and lib.is_prime_power(q)]
        if qs:
            visits = qs[:2] + qs
            chunk = max(1.5, 0.09 * time_limit)
            _gq_growth(d, D, visits, rng, deadline, consider, chunk)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
