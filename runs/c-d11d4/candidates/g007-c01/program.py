import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Classical bases (fallback and calibration).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW FAMILY: vertex-transitive bipartite Cayley graphs.
#
# Group G = Z_m x|_r Z_k (element (a, b) coded as a*k + b). For a set S of d
# distinct group elements, the bipartite graph has sides A and B, with
# a_g adjacent to b_{g s} for s in S. Left multiplication by h is an
# automorphism that maps a_g -> a_{hg} and b_g -> b_{hg}. Therefore
#   - all A-A distances come from BFS at a_e,
#   - all A-B distances come from BFS at a_e,
#   - all B-B distances come from BFS at b_e.
# Two BFS runs over 2|G| vertices decide diameter <= D exactly.
# ----------------------------------------------------------------------------

def _rperm(m, k, r, c, dd):
    """Array R with R[g] = code of g * (c, dd) in Z_m x|_r Z_k."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    A = x // k
    B = x % k
    P = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    na = (A + P[B] * c) % m
    nb = (B + dd) % k
    return na * k + nb


def _inv_code(m, k, r, s):
    """Code of the inverse of element s (coded as c*k + dd)."""
    c, dd = divmod(s, k)
    ic = (-c * pow(r, (-dd) % k, m)) % m
    idd = (-dd) % k
    return ic * k + idd


def _cayley_bad(m, k, r, S, D):
    """Number of (ordered-root) vertices not within distance D; 0 iff the Cayley graph has diameter <= D."""
    G = m * k
    R = []
    Ri = []
    for s in S:
        c, dd = divmod(s, k)
        R.append(_rperm(m, k, r, c, dd))
        ic, idd = divmod(_inv_code(m, k, r, s), k)
        Ri.append(_rperm(m, k, r, ic, idd))
    bad = 0
    for root in (0, 1):
        vis = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        vis[root][0] = True
        front = np.zeros(1, dtype=np.int64)
        side = root
        for _ in range(D):
            if front.size == 0:
                break
            maps = R if side == 0 else Ri
            nxt = np.unique(np.concatenate([mp[front] for mp in maps]))
            nxt = nxt[~vis[1 - side][nxt]]
            vis[1 - side][nxt] = True
            front = nxt
            side = 1 - side
        if root == 0:
            bad += 2 * G - int(vis[0].sum() + vis[1].sum())
        else:
            bad += G - int(vis[1].sum())
    return bad


def _cayley_search(m, k, r, d, D, rng, iters, deadline):
    """Hill-climb a d-element connection set S in the group so the Cayley graph has diameter <= D."""
    G = m * k
    if d > G:
        return None
    S = rng.sample(range(G), d)
    c = _cayley_bad(m, k, r, S, D)
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        cand = rng.randrange(G)
        if cand in S:
            continue
        T = S[:]
        T[i] = cand
        ct = _cayley_bad(m, k, r, T, D)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _cayley_graph(m, k, r, S):
    """Build (n, edges): side A codes 0..G-1, side B codes G..2G-1, a_g ~ b_{g s}."""
    G = m * k
    edges = []
    for s in S:
        c, dd = divmod(s, k)
        Rs = _rperm(m, k, r, c, dd).tolist()
        for g in range(G):
            edges.append((g, G + Rs[g]))
    return 2 * G, edges


def _groups_of_order(G):
    """All (m, k, r) with m*k = G giving semidirect products Z_m x|_r Z_k; cyclic group first."""
    out = [(G, 1, 1)]
    for k in range(2, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _cayley_phase(d, D, best_n, rng, deadline):
    """Search Cayley bipartite graphs of increasing order above best_n. Returns (n, edges) or None."""
    best = None
    lo = best_n // 2 + 1
    fails = 0
    while time.monotonic() < deadline:
        G = lo + rng.randrange(0, 12 + fails // 8)
        if G < d:
            G = d
        groups = _groups_of_order(G)
        hit = None
        for _ in range(3):
            if time.monotonic() >= deadline:
                break
            m, k, r = groups[rng.randrange(len(groups))]
            S = _cayley_search(m, k, r, d, D, rng, 300, deadline)
            if S is not None:
                hit = (m, k, r, S)
                break
            fails += 1
        if hit is not None:
            n, e = _cayley_graph(*hit)
            if lib.is_valid(n, e, d, D):
                best = (n, e)
                lo = G + 1
    return best


# ----------------------------------------------------------------------------
# Twin extension. A twin v of x (same side, N(v) = N(x)) keeps all old distances,
# has dist(v, x) = 2, and preserves bipartiteness. It needs one spare degree on
# each neighbour of x. Twins are added greedily in random passes until none remain.
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


# ----------------------------------------------------------------------------
# Cover-based vertex extension.
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


# ----------------------------------------------------------------------------
# Rarity-weighted set cover (numpy).
# ----------------------------------------------------------------------------

def _ball_rows(ball, idx, n):
    """float32 membership matrix: row r is the ball (as 0/1 vector over n vertices) of idx[r]."""
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


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices FIRST, then saturate edges with the remaining spare degree."""
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
# Voltage lifts over NON-cyclic groups (semidirect products Z_m x| Z_k2).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
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
    """Hill-climb dart voltages in a group of order about G over a random d-regular base."""
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


# ----------------------------------------------------------------------------
# Haar and cyclic-lift families (secondary, for the leftover time).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
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
    """Hill-climb Z_m voltages on a random d-regular bipartite base with k+k vertices."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
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

    # D == 3: projective-plane based growth (skipped for D == 4, where W(q) is used).
    if D >= 3 and D != 4:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            t0 = time.monotonic()
            span = max(0.0, 0.25 * T - (t0 - start))
            for i, q in enumerate(pg_qs):
                try:
                    pg_n, pg_e = lib.projective_plane_incidence(q)
                    consider(pg_n, pg_e)
                    slice_end = t0 + span * (i + 1) / len(pg_qs)
                    n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
                    consider(n2, e2)
                except Exception:
                    pass

    # Calibration: already at the Moore bound, nothing to gain.
    if best_n >= lib.moore_bound(d, D):
        return best

    # D == 4 target: new Cayley-family search first, then W(q) pipeline growth.
    if D >= 4:
        gq = None
        try:
            gq = _best_gq(d)
        except Exception:
            gq = None
        if gq is not None:
            consider(gq[0], gq[1])

        cayley_end = start + 0.58 * T
        try:
            res = _cayley_phase(d, D, best_n, rng, cayley_end)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

        base_end = start + 0.80 * T
        if gq is not None:
            cur = None
            while time.monotonic() < base_end:
                if cur is None or rng.random() < 0.2:
                    src_n, src_e = gq[0], gq[1]
                else:
                    src_n, src_e = _remove_twins(cur[0], cur[1], 0.15, rng)
                try:
                    pn, pe = _pipeline(src_n, src_e, d, D, base_end, rng)
                    consider(pn, pe)
                    if cur is None or pn >= cur[0]:
                        cur = (pn, pe)
                except Exception:
                    break

    # Leftover search for every case (voltage lifts and Haar graphs).
    deadline = start + 0.88 * T
    group_p = 0.85 if D >= 4 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < deadline:
        r = rng.random()
        try:
            if r < group_p:
                k = rng.choice(group_sizes)
                st = group_state[k]
                floor = best_n // (2 * k) + 1
                G = max(st["G"], floor, 2)
                res = _group_search(d, D, k, G, rng, 200, deadline)
                if res is not None:
                    consider(res[0], res[1])
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
                    haar_miss = 0
                else:
                    haar_miss += 1
                haar_m += 1
            else:
                k = rng.choice(base_sizes)
                m = max(ladder[k], best_n // (2 * k) + 1, 2)
                res = _search_lift(d, D, k, m, rng, 250, deadline)
                if res is not None:
                    consider(res[0], res[1])
                    ladder[k] = m + 1
                else:
                    ladder[k] = m
        except Exception:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
