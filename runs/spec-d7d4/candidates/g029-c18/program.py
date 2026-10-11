import itertools
import math
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
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4.
    Points are 0..P-1, lines are P..2P-1; every vertex has degree q+1."""
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
# Twin blow-up with spare-capacity packing.
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
# Cover-based vertex extension (diameter-preserving growth).
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


def _exact_ball_cover(cands, ball, full, d, budget):
    """Branch-and-bound exact cover of the bitmask `full` by at most d candidate balls."""
    nodes = [0]

    def rec(covered, chosen):
        unc = full & ~covered
        if unc == 0:
            return chosen
        room = d - len(chosen)
        if room <= 0:
            return None
        nodes[0] += 1
        if nodes[0] > budget:
            return None
        gains = [(ball[s] & unc).bit_count() for s in cands]
        mx = max(gains, default=0)
        if mx == 0 or unc.bit_count() > room * mx:
            return None
        w = (unc & -unc).bit_length() - 1
        opts = [i for i, s in enumerate(cands) if gains[i] > 0 and (ball[s] >> w) & 1]
        opts.sort(key=lambda i: -gains[i])
        for i in opts:
            res = rec(covered | ball[cands[i]], chosen + [cands[i]])
            if res is not None:
                return res
            if nodes[0] > budget:
                return None
        return None

    return rec(0, [])


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
            if D >= 4 and time.monotonic() < deadline:
                chosen = _exact_ball_cover(cands, ball, full, d, 2000)
            if not chosen:
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


def _grow(n, edges, d, D, deadline, rng, always_random=False):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, always_random)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _expand(n, edges, d, D, deadline, rng, rounds=6):
    """Alternate twin packing on both sides with cover growth, while the graph keeps growing."""
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
# NEW: deletion-saturation search inside a denser generalized quadrangle.
#
# W(q) with q = d is (d+1)-regular. Keep an induced subgraph on a vertex set K,
# trim any vertex that still has degree d+1 (drop edges to its busiest neighbour),
# then saturate spare degree with random opposite-side edges. The induced graph
# is bipartite and has max degree d by construction. A simulated annealing walk
# swaps kept and removed vertices to minimize the number of pairs at distance > D.
# Whenever the cost reaches zero, the order grows by one and the walk continues.
# ----------------------------------------------------------------------------

def _induced_graph(K, base_adj, P, d, rng_seed=7):
    """Return (N, nb) for the subgraph of the base induced on sorted list K, degree <= d."""
    N = len(K)
    idx = {v: i for i, v in enumerate(K)}
    side = [0 if v < P else 1 for v in K]
    nb = [set() for _ in range(N)]
    for i, v in enumerate(K):
        for u in base_adj[v]:
            j = idx.get(u)
            if j is not None:
                nb[i].add(j)
    # Trim over-degree vertices, removing edges to their busiest neighbours.
    for i in range(N):
        while len(nb[i]) > d:
            j = max(nb[i], key=lambda x: (len(nb[x]), x))
            nb[i].discard(j)
            nb[j].discard(i)
    # Saturate spare degree with random opposite-side non-edges.
    rnd = random.Random(rng_seed)
    left = [i for i in range(N) if side[i] == 0 and len(nb[i]) < d]
    right = [i for i in range(N) if side[i] == 1 and len(nb[i]) < d]
    for a in left:
        for _ in range(12):
            if len(nb[a]) >= d or not right:
                break
            b = right[rnd.randrange(len(right))]
            if b in nb[a] or len(nb[b]) >= d:
                continue
            nb[a].add(b)
            nb[b].add(a)
        right = [b for b in right if len(nb[b]) < d]
    return N, nb


def _bad_count(N, nb, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    adj = [list(s) for s in nb]
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _del_eval(kept, base_adj, P, d, D):
    """Return (cost, N, edges) for the saturated induced subgraph on kept vertices."""
    K = sorted(kept)
    N, nb = _induced_graph(K, base_adj, P, d)
    cost = _bad_count(N, nb, D)
    edges = [(i, j) for i in range(N) for j in nb[i] if i < j]
    return cost, N, edges


def _del_search(base_adj, P, d, D, n_start, deadline, rng, consider):
    """Annealed swap walk over kept sets; grows the order whenever the diameter is met."""
    total = 2 * P
    perm = list(range(total))
    rng.shuffle(perm)
    kept = perm[:n_start]
    removed = perm[n_start:]
    c, _, _ = _del_eval(kept, base_adj, P, d, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while time.monotonic() < deadline:
        if c == 0:
            _, N, e = _del_eval(kept, base_adj, P, d, D)
            consider(N, e)
            if not removed:
                break
            k = rng.randrange(len(removed))
            kept.append(removed[k])
            removed[k] = removed[-1]
            removed.pop()
            c, _, _ = _del_eval(kept, base_adj, P, d, D)
            continue
        frac = (time.monotonic() - t0) / span
        T = (0.1 * (1.0 - frac) + 0.005) * max(c, 1)
        i = rng.randrange(len(kept))
        j = rng.randrange(len(removed))
        kept[i], removed[j] = removed[j], kept[i]
        c2, _, _ = _del_eval(kept, base_adj, P, d, D)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            c = c2
        else:
            kept[i], removed[j] = removed[j], kept[i]


# ----------------------------------------------------------------------------
# Iterated local search: delete a random vertex, repair the diameter with
# saturation edges if needed, regrow with cover vertices. Accept when the order
# does not drop; store only verified records.
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
    """Repeatedly add cover vertices while possible, then saturate spare slots."""
    while time.monotonic() < deadline:
        r = _add_one(n, edges, d, D, rng)
        if r is None:
            break
        n, edges = r
    edges = _saturate_edges(n, edges, d, rng)
    return n, edges


def _ils(n, edges, d, D, deadline, rng, holder):
    """Iterated local search; holder[0] is the best verified (n, edges) so far."""
    cn, ce = n, list(edges)
    while time.monotonic() < deadline:
        x = rng.randrange(cn)
        rn, re = _remove_vertex(cn, ce, x)
        if rn <= 0:
            continue
        if not lib.within_diameter(rn, re, D):
            re = _saturate_edges(rn, re, d, rng)
            if not lib.within_diameter(rn, re, D):
                continue
        rn, re = _fill(rn, re, d, D, rng, deadline)
        if rn >= cn:
            cn, ce = rn, re
            if rn > holder[0][0] and lib.is_valid(rn, re, d, D):
                holder[0] = (rn, re)


# ----------------------------------------------------------------------------
# Driver.
# Phases (fractions of the usable budget):
#   0.00 - 0.35  cover/twin expansion of the base graphs (and PG bases for D = 3)
#   0.35 - 0.82  deletion-saturation annealing inside W(d) for D = 4 (new)
#   0.82 - 1.00  iterated local search on the best graph
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 1.0)
    deadline = start + total
    t_expand = start + 0.35 * total
    t_del = start + 0.82 * total
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

    # Calibration shortcut: already at the Moore bound, nothing to gain.
    if best[0] >= lib._moore_bound(d, D):
        return best

    bases = []
    del_base = None
    try:
        if D == 3:
            bases = _best_pg(d, 2)
            for b in bases:
                consider(b[0], b[1])
        elif D >= 4:
            qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
            for q in qs:
                if time.monotonic() >= t_expand:
                    break
                gq = _gq_w(q)
                bases.append(gq)
                consider(gq[0], gq[1])
            # New: the denser quadrangle W(d) (degree d+1) is the source for deletion search.
            if D == 4 and 4 <= d <= 12 and lib.is_prime_power(d):
                del_base = _gq_w(d)
    except Exception:
        pass

    if best[0] >= lib._moore_bound(d, D):
        return best

    # Phase 1: twin packing and cover growth on the bases, mixed with the best graph.
    try:
        rot = 0
        while bases and time.monotonic() < t_expand:
            if best[0] > 0 and rng.random() < 0.3:
                src = best
            else:
                src = bases[rot % len(bases)]
                rot += 1
            slice_end = min(t_expand, time.monotonic() + 0.12 * total)
            n2, e2 = _expand(src[0], src[1], d, D, slice_end, rng)
            consider(n2, e2)
    except Exception:
        pass

    # Phase 2 (new): deletion-saturation annealing inside W(d).
    try:
        if del_base is not None and time.monotonic() < t_del:
            n_w, e_w = del_base
            P = n_w // 2
            base_adj = _adjacency(n_w, e_w)
            n_start = max(4, best[0] - 40)
            _del_search(base_adj, P, d, D, n_start, t_del, rng, consider)
    except Exception:
        pass

    # Phase 3: iterated local search on the best graph found.
    try:
        if time.monotonic() < deadline and best[0] >= 2:
            holder = [best]
            _ils(best[0], best[1], d, D, deadline, rng, holder)
            if holder[0][0] > best[0] and lib.is_valid(holder[0][0], holder[0][1], d, D):
                best = holder[0]
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
