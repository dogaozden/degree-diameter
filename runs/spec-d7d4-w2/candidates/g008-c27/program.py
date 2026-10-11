import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d, count=1):
    """Incidence graphs of PG(2, q) for the largest prime powers q with q + 1 <= d."""
    out = []
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
            if len(out) == count:
                break
    return out


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


# ----------------------------------------------------------------------------
# Graph utilities.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
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
    """Bitmask per vertex of all vertices within distance r (r = 0 gives the vertex itself)."""
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


# ----------------------------------------------------------------------------
# Twin blow-up with spare-capacity packing (from the parent).
#
# Twinning v gives v' with the same neighbourhood; distances among old vertices
# are unchanged and bipartiteness is kept. A whole side is twinned at once as a
# packing problem over the spare degrees of the other side.
# ----------------------------------------------------------------------------

def _pack(R, cap, n, rng, deadline, iters):
    """Choose candidates so that each resource u is used by at most cap[u] chosen candidates."""
    k = len(R)
    if k == 0:
        return []
    users = [[] for _ in range(n)]
    for i, r in enumerate(R):
        for u in r:
            users[u].append(i)
    load = [0] * n
    inS = [False] * k
    S = set()

    def add(i):
        inS[i] = True
        S.add(i)
        for u in R[i]:
            load[u] += 1

    def remove(i):
        inS[i] = False
        S.discard(i)
        for u in R[i]:
            load[u] -= 1

    order = list(range(k))
    rng.shuffle(order)
    for i in order:
        if all(load[u] < cap[u] for u in R[i]):
            add(i)
    best = list(S)

    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        i = rng.randrange(k)
        if inS[i]:
            continue
        removed = []
        for u in R[i]:
            while load[u] >= cap[u]:
                j = rng.choice([x for x in users[u] if inS[x]])
                remove(j)
                removed.append(j)
        add(i)
        delta = 1 - len(removed)
        if delta < 0 and rng.random() >= 0.03:
            remove(i)
            for j in removed:
                add(j)
        if len(S) > len(best):
            best = list(S)
    return best


def _exact_cover(R, universe, users, deadline, node_cap):
    """Find candidates whose resource sets partition `universe` exactly (DFS, node-limited)."""
    covered = set()
    chosen = []
    nodes = [0]

    def rec():
        if len(covered) == len(universe):
            return True
        nodes[0] += 1
        if nodes[0] > node_cap or time.monotonic() > deadline:
            return False
        best_opts = None
        for u in universe:
            if u in covered:
                continue
            opts = [i for i in users[u] if all(r not in covered for r in R[i])]
            if not opts:
                return False
            if best_opts is None or len(opts) < len(best_opts):
                best_opts = opts
        for i in best_opts:
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


def _twin_pass(n, edges, d, side, rng, deadline, iters):
    """Twin as many vertices of one side as the spare degree of the other side allows."""
    adj = _adjacency(n, edges)
    color = _bipartition(n, adj)
    deg = [len(a) for a in adj]
    capv = [d - deg[u] for u in range(n)]
    cands = [v for v in range(n)
             if color[v] == side and adj[v] and all(capv[u] >= 1 for u in adj[v])]
    if not cands:
        return n, edges
    R = [adj[v] for v in cands]
    universe = sorted({u for r in R for u in r})

    chosen = None
    if all(capv[u] == 1 for u in universe):
        users = [[] for _ in range(n)]
        for i, r in enumerate(R):
            for u in r:
                users[u].append(i)
        ex = _exact_cover(R, universe, users, deadline, 3000)
        if ex is not None:
            chosen = ex
    pk = _pack(R, capv, n, rng, deadline, iters)
    if chosen is None or len(pk) > len(chosen):
        chosen = pk
    if not chosen:
        return n, edges

    new_edges = list(edges)
    nn = n
    for i in chosen:
        v = cands[i]
        for u in adj[v]:
            new_edges.append((u, nn))
        nn += 1
    return nn, new_edges


# ----------------------------------------------------------------------------
# NEW: pair gadget growth.
#
# Add two new vertices a (on side 0) and b (on side 1) joined by the edge a-b,
# with S_a a subset of side 1 and S_b a subset of side 0, |S_a|, |S_b| <= d-1.
# The new graph's distances are exact in terms of old distances:
#   dist(a, u) = min(1 + dist(S_a, u), 2 + dist(S_b, u)),
#   dist(b, u) = min(1 + dist(S_b, u), 2 + dist(S_a, u)).
# So u is covered iff (A1 | B2) and (B1 | A2), where A1 = ball(S_a, D-1),
# A2 = ball(S_a, D-2), and B1, B2 are the analogues for S_b. Old-old distances
# can only shrink, so validity is preserved exactly. Per old vertex this costs
# 2(d-1) spare slots for two new vertices, cheaper than single cover (d per vertex).
# ----------------------------------------------------------------------------

def _pair_cover(R1, R2, Ca, Cb, d, full, rng, randomize):
    """Greedy choice of S_a in Ca and S_b in Cb covering all vertices; returns (S_a, S_b) or None."""
    pa = list(Ca)
    pb = list(Cb)
    if randomize:
        rng.shuffle(pa)
        rng.shuffle(pb)
    cap = d - 1
    A1 = A2 = B1 = B2 = 0
    covmask = 0
    Sa, Sb = [], []
    while covmask != full and (len(Sa) < cap or len(Sb) < cap):
        bestv = covmask.bit_count()
        choice = None
        bestmask = covmask
        if len(Sa) < cap:
            for s in pa:
                m = ((A1 | R1[s] | B2) & (B1 | A2 | R2[s]))
                v = m.bit_count()
                if v > bestv:
                    bestv, choice, bestmask = v, (0, s), m
        if len(Sb) < cap:
            for s in pb:
                m = ((A1 | B2 | R2[s]) & (B1 | R1[s] | A2))
                v = m.bit_count()
                if v > bestv:
                    bestv, choice, bestmask = v, (1, s), m
        if choice is None:
            break
        side, s = choice
        if side == 0:
            A1 |= R1[s]
            A2 |= R2[s]
            Sa.append(s)
            pa.remove(s)
        else:
            B1 |= R1[s]
            B2 |= R2[s]
            Sb.append(s)
            pb.remove(s)
        covmask = bestmask
    if covmask == full:
        return Sa, Sb
    return None


def _pair_grow(n, edges, d, D, deadline, rng):
    """Repeatedly add pair gadgets while a covering pair exists (exact diameter preservation)."""
    if D < 3:
        return n, edges
    edges = list(edges)
    while time.monotonic() < deadline:
        adj = _adjacency(n, edges)
        color = _bipartition(n, adj)
        deg = [len(a) for a in adj]
        R1 = _balls_radius(n, adj, D - 1)
        R2 = _balls_radius(n, adj, D - 2)
        full = (1 << n) - 1
        Ca = [s for s in range(n) if color[s] == 1 and deg[s] < d]
        Cb = [s for s in range(n) if color[s] == 0 and deg[s] < d]
        if not Ca or not Cb:
            break
        res = None
        for att in range(6):
            res = _pair_cover(R1, R2, Ca, Cb, d, full, rng, att > 0)
            if res is not None:
                break
        if res is None:
            break
        Sa, Sb = res
        a, b = n, n + 1
        for s in Sa:
            edges.append((s, a))
        for s in Sb:
            edges.append((s, b))
        edges.append((a, b))
        n += 2
    return n, edges


# ----------------------------------------------------------------------------
# Cover-based single-vertex extension (diameter-preserving growth).
# ----------------------------------------------------------------------------

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


def _extend_cover(n, edges, d, D, deadline, rng, always_random=False):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = _adjacency(n, edges)
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
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng,
                                       always_random or attempt > 0)
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
    """Add random edges between non-adjacent opposite-side vertices with spare degree."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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
    """Alternate pair gadgets and single cover vertices. Spare slots are NOT saturated here,
    since saturation would consume capacity that later growth could use."""
    cur_n, cur_e = n, list(edges)
    for _ in range(20):
        if time.monotonic() >= deadline:
            break
        n0 = cur_n
        cur_n, cur_e = _pair_grow(cur_n, cur_e, d, D, deadline, rng)
        cur_n, cur_e = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == n0:
            break
    return cur_n, cur_e


def _expand(n, edges, d, D, deadline, rng, rounds=6):
    """Alternate twin packing on both sides with growth, while the graph keeps growing."""
    cur_n, cur_e = n, list(edges)
    for _ in range(rounds):
        if time.monotonic() >= deadline:
            break
        n0 = cur_n
        for side in (0, 1):
            iters = rng.choice([3000, 10000, 30000])
            cur_n, cur_e = _twin_pass(cur_n, cur_e, d, side, rng, deadline, iters)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == n0:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Iterated local search with vertex excision and regrowth.
#
# A move deletes a random vertex (the last vertex takes its label). If the
# diameter breaks, random saturation edges are tried as repair. The graph is
# then regrown with pair gadgets and single covers. Moves that keep the order
# are accepted (plateau drift); a one-vertex loss is accepted rarely and only
# within 2 of the best order.
# ----------------------------------------------------------------------------

def _remove_vertex(n, edges, x):
    """Delete vertex x; the last vertex takes its label. Returns (n-1, edges)."""
    last = n - 1

    def m(v):
        return x if v == last else v

    new = [(m(u), m(v)) for u, v in edges if u != x and v != x]
    return n - 1, new


def _add_one(n, edges, d, D, rng):
    """Add one vertex by a degree-respecting cover; return (n+1, edges) or None."""
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    ball = _balls_radius(n, adj, D - 1)
    full = (1 << n) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(n) if color[s] == c and deg[s] < d]
        if not cands:
            continue
        chosen = None
        for attempt in range(30):
            chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
            if chosen:
                break
        if chosen:
            v = n
            new_edges = list(edges)
            for s in chosen:
                new_edges.append((s, v))
            return n + 1, new_edges
    return None


def _fill(n, edges, d, D, rng, deadline):
    """Alternate pair gadgets and single cover vertices until neither adds anything."""
    while time.monotonic() < deadline:
        n0 = n
        n, edges = _pair_grow(n, edges, d, D, deadline, rng)
        r = _add_one(n, edges, d, D, rng)
        if r is not None:
            n, edges = r
        elif n == n0:
            break
    return n, edges


def _ils(n, edges, d, D, deadline, rng, holder):
    """Iterated local search; holder[0] is the best verified (n, edges) so far."""
    cn, ce = n, list(edges)
    while time.monotonic() < deadline:
        if cn < 3:
            break
        x = rng.randrange(cn)
        rn, re_ = _remove_vertex(cn, ce, x)
        if rn <= 1:
            continue
        if not lib.within_diameter(rn, re_, D):
            re_ = _saturate_edges(rn, re_, d, rng)
            if not lib.within_diameter(rn, re_, D):
                continue
        rn, re_ = _fill(rn, re_, d, D, rng, deadline)
        floor = holder[0][0] - 2
        if rn >= cn or (rn == cn - 1 and rn >= floor and rng.random() < 0.05):
            if not lib.within_diameter(rn, re_, D):
                continue
            cn, ce = rn, re_
            if rn > holder[0][0] and lib.is_valid(rn, re_, d, D):
                holder[0] = (rn, re_)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    expand_deadline = start + 0.35 * time_limit
    search_deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    bases = []
    if D == 3:
        bases = [b for b in _best_pg(d, 2)]
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= expand_deadline:
                break
            bases.append(_gq_w(q))

    for b in bases:
        consider(b[0], b[1])

    # Calibration shortcut: already at the Moore bound, nothing to gain.
    if best[0] >= lib._moore_bound(d, D):
        return best

    rot = 0
    while bases and time.monotonic() < expand_deadline:
        if best[0] > 0 and rng.random() < 0.3:
            src = best
        else:
            src = bases[rot % len(bases)]
            rot += 1
        n2, e2 = _expand(src[0], src[1], d, D, expand_deadline, rng)
        consider(n2, e2)

    # Phase 2: iterated local search on the best graph found.
    if time.monotonic() < search_deadline and best[0] >= 2:
        holder = [best]
        _ils(best[0], best[1], d, D, search_deadline, rng, holder)
        if holder[0][0] > best[0] and lib.is_valid(holder[0][0], holder[0][1], d, D):
            best = holder[0]

    return best
