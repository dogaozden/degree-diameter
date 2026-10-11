import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
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

    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Shared utilities.
# ----------------------------------------------------------------------------

def _adj_list(n, edges):
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
    """Pick at most d candidates whose radius balls cover `full`; None if impossible."""
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
# Maximum independent set by iterated local search (ARW-style (1,2)-swaps).
# conf[v] lists the conflicts of v. Returns a list of vertex indices.
# ----------------------------------------------------------------------------

def _mis(conf, rng, deadline, max_iter):
    N = len(conf)
    confset = [set(c) for c in conf]
    inS = [False] * N
    tight = [0] * N
    S = set()

    def add(v):
        inS[v] = True
        S.add(v)
        for w in conf[v]:
            tight[w] += 1

    def rem(v):
        inS[v] = False
        S.discard(v)
        for w in conf[v]:
            tight[w] -= 1

    def fill():
        order = list(range(N))
        rng.shuffle(order)
        for v in order:
            if not inS[v] and tight[v] == 0:
                add(v)

    def local():
        improved = True
        while improved and time.monotonic() < deadline:
            improved = False
            order = list(S)
            rng.shuffle(order)
            for x in order:
                if not inS[x]:
                    continue
                cand = [u for u in conf[x] if not inS[u] and tight[u] == 1]
                pair = None
                for i in range(len(cand)):
                    for j in range(i + 1, len(cand)):
                        if cand[j] not in confset[cand[i]]:
                            pair = (cand[i], cand[j])
                            break
                    if pair:
                        break
                if pair:
                    rem(x)
                    add(pair[0])
                    add(pair[1])
                    fill()
                    improved = True

    fill()
    local()
    best = list(S)
    it = 0
    while it < max_iter and time.monotonic() < deadline:
        it += 1
        v = rng.randrange(N)
        if inS[v]:
            continue
        for w in conf[v]:
            if inS[w]:
                rem(w)
        add(v)
        fill()
        local()
        if len(S) > len(best):
            best = list(S)
        elif len(S) < len(best) - 1 or (len(S) < len(best) and rng.random() < 0.1):
            for x in list(S):
                rem(x)
            for x in best:
                add(x)
    return best


# ----------------------------------------------------------------------------
# Exact cover of resources by candidates (randomized DFS, node-limited).
# ----------------------------------------------------------------------------

def _exact_once(R, users, universe, rng, node_cap, deadline):
    covered = set()
    chosen = []
    nodes = [0]

    def rec():
        if len(covered) == len(universe):
            return True
        nodes[0] += 1
        if nodes[0] > node_cap or time.monotonic() > deadline:
            return False
        pick = None
        for u in universe:
            if u in covered:
                continue
            opts = [i for i in users[u] if all(r not in covered for r in R[i])]
            if not opts:
                return False
            if pick is None or len(opts) < len(pick):
                pick = opts
        rng.shuffle(pick)
        for i in pick:
            for r in R[i]:
                covered.add(r)
            chosen.append(i)
            if rec():
                return True
            chosen.pop()
            for r in R[i]:
                covered.discard(r)
        return False

    return list(chosen) if rec() else None


# ----------------------------------------------------------------------------
# Twin packing.
#
# A twin of x has the same neighbourhood as x. It keeps the diameter and
# bipartiteness, and needs one spare slot on every neighbour. Twins of side 0
# use slack on side 1 and twins of side 1 use slack on side 0, so the two
# sides are independent.
# ----------------------------------------------------------------------------

def _greedy_packing(cands, adj, cap, n, rng, end):
    best = []
    tries = 0
    while time.monotonic() < end and tries < 300:
        tries += 1
        order = list(range(len(cands)))
        rng.shuffle(order)
        load = [0] * n
        chosen = []
        for i in order:
            x = cands[i]
            if all(load[u] < cap[u] for u in adj[x]):
                for u in adj[x]:
                    load[u] += 1
                chosen.append(i)
        if len(chosen) > len(best):
            best = chosen
    return best


def _side_twins(n, adj, color, d, side, rng, ex_end, end):
    """Return the vertices of `side` to twin (chosen from the original graph)."""
    cap = [d - len(adj[u]) for u in range(n)]
    cands = [x for x in range(n) if color[x] == side and adj[x]
             and all(cap[u] >= 1 for u in adj[x])]
    if not cands:
        return []
    uniform = all(cap[u] == 1 for x in cands for u in adj[x])
    if not uniform:
        idx = _greedy_packing(cands, adj, cap, n, rng, end)
        return [cands[i] for i in idx]

    users = {}
    for i, x in enumerate(cands):
        for u in adj[x]:
            users.setdefault(u, []).append(i)
    R = [adj[x] for x in cands]
    best = []
    perfect = False
    sizes = {len(r) for r in R}
    if len(sizes) == 1:
        r = sizes.pop()
        if len(users) % r == 0:
            universe = list(users)
            target = len(universe) // r
            while time.monotonic() < ex_end:
                sol = _exact_once(R, users, universe, rng, 1500, ex_end)
                if sol is not None:
                    best = sol
                    perfect = len(sol) == target
                    break
    if not perfect:
        conf = [set() for _ in range(len(cands))]
        for lst in users.values():
            for a in lst:
                for b in lst:
                    if a != b:
                        conf[a].add(b)
        conf = [sorted(s) for s in conf]
        mis = _mis(conf, rng, end, 15000)
        if len(mis) > len(best):
            best = mis
    return [cands[i] for i in best]


def _twin_graph(n, edges, d, rng, end):
    adj = _adj_list(n, edges)
    color = _bipartition(n, adj)
    now = time.monotonic()
    span = max(0.0, end - now)
    c0 = _side_twins(n, adj, color, d, 0, rng,
                     now + 0.1 * span, now + 0.5 * span)
    now2 = time.monotonic()
    span2 = max(0.0, end - now2)
    c1 = _side_twins(n, adj, color, d, 1, rng,
                     now2 + 0.25 * span2, end)
    E = list(edges)
    nn = n
    for x in c0 + c1:
        for u in adj[x]:
            E.append((u, nn))
        nn += 1
    return nn, E


# ----------------------------------------------------------------------------
# Cover-based vertex growth (diameter-preserving).
# A new vertex joined to S keeps diameter D iff the radius-(D-1) balls of S
# cover every vertex.
# ----------------------------------------------------------------------------

def _cover_grow(n, edges, d, D, deadline, rng):
    edges = list(edges)
    while time.monotonic() < deadline:
        adj = _adj_list(n, edges)
        deg = [len(a) for a in adj]
        color = _bipartition(n, adj)
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        grown = False
        for c in rng.sample([0, 1], 2):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for att in range(40):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, att > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                for s in chosen:
                    edges.append((s, v))
                grown = True
                break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best
    if d == 2:
        cyc = [(i, (i + 1) % (2 * D)) for i in range(2 * D)]
        consider(2 * D, cyc)
        return best

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    bases = []
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            bases.append(pg)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                bases.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    else:
        q = next((q for q in range(min(d - 1, 8), 1, -1) if lib.is_prime_power(q)), None)
        if q is not None:
            try:
                bases.append(_gq_w(q))
            except Exception:
                pass

    for b in bases:
        consider(b[0], b[1])

    for b in bases:
        if time.monotonic() > start + 0.8 * T or best[0] >= moore:
            break
        try:
            tn, te = _twin_graph(b[0], b[1], d, rng, start + 0.35 * T)
            consider(tn, te)
            gn, ge = _cover_grow(tn, te, d, D, start + 0.45 * T, rng)
            consider(gn, ge)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
