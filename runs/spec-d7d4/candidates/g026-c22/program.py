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
# Cover-based vertex extension (diameter-preserving growth).
# A new vertex joined to a cover of all vertices within distance D-1 keeps the
# diameter at most D.
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


def _extend_cover(n, edges, d, D, deadline, rng):
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
            for attempt in range(60):
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


# ----------------------------------------------------------------------------
# NEW: degree-preserving 2-switch annealing for vertex insertion.
#
# After adding a vertex, the diameter may be violated. Instead of requiring a
# perfect cover, we anneal over bipartite 2-switches (a,b),(c,e) -> (a,e),(c,b)
# with a,c on one side. Switches keep every degree and the bipartition, so the
# search can reshape the graph around the new vertex. Cost is the number of
# ordered vertex pairs at distance > D (zero means valid). Spare degree is also
# used by add-edge moves, and removal moves create spare degree.
# ----------------------------------------------------------------------------

def _bad_count(n, adj, D):
    """Ordered pairs (x, y) with dist(x, y) > D, via bitmask balls over sets adj."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _sw(adj, a, b, c, e):
    """Remove (a,b),(c,e) and add (a,e),(c,b). Undo with _sw(adj, a, e, c, b)."""
    adj[a].discard(b)
    adj[b].discard(a)
    adj[c].discard(e)
    adj[e].discard(c)
    adj[a].add(e)
    adj[e].add(a)
    adj[c].add(b)
    adj[b].add(c)


def _switch_sa(n, adj, color, d, D, deadline, rng):
    """Anneal adj (list of sets, mutated in place) to zero bad pairs. True on success."""
    L = [v for v in range(n) if color[v] == 0]
    R = [v for v in range(n) if color[v] == 1]
    cur = _bad_count(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 4.0, 0.6
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return False
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        x = rng.random()
        if x < 0.80:
            a = rng.choice(L)
            c = rng.choice(L)
            if a == c or not adj[a] or not adj[c]:
                continue
            b = rng.choice(tuple(adj[a]))
            e = rng.choice(tuple(adj[c]))
            if e in adj[a] or b in adj[c]:
                continue
            _sw(adj, a, b, c, e)
            new = _bad_count(n, adj, D)
            if new <= cur or rng.random() < math.exp((cur - new) / T):
                cur = new
            else:
                _sw(adj, a, e, c, b)
        elif x < 0.95:
            a = rng.choice(L)
            e = rng.choice(R)
            if len(adj[a]) >= d or len(adj[e]) >= d or e in adj[a]:
                continue
            adj[a].add(e)
            adj[e].add(a)
            new = _bad_count(n, adj, D)
            if new <= cur or rng.random() < math.exp((cur - new) / T):
                cur = new
            else:
                adj[a].discard(e)
                adj[e].discard(a)
        else:
            a = rng.choice(L)
            if not adj[a]:
                continue
            e = rng.choice(tuple(adj[a]))
            adj[a].discard(e)
            adj[e].discard(a)
            new = _bad_count(n, adj, D)
            if new <= cur or rng.random() < math.exp((cur - new) / T):
                cur = new
            else:
                adj[a].add(e)
                adj[e].add(a)
    return True


def _switch_grow(n, edges, d, D, deadline, rng):
    """Repeatedly add one vertex and anneal with switches; keep the last success."""
    good_n, good_e = n, list(edges)
    while time.monotonic() < deadline:
        adj = [set() for _ in range(good_n)]
        for u, v in good_e:
            adj[u].add(v)
            adj[v].add(u)
        color = _bipartition(good_n, [list(s) for s in adj])
        c = rng.randrange(2)
        spare = [w for w in range(good_n) if color[w] == c and len(adj[w]) < d]
        if not spare:
            c = 1 - c
            spare = [w for w in range(good_n) if color[w] == c and len(adj[w]) < d]
        if not spare:
            break
        rng.shuffle(spare)
        k = min(d, len(spare))
        v = good_n
        adj.append(set(spare[:k]))
        for w in spare[:k]:
            adj[w].add(v)
        color.append(1 - c)
        now = time.monotonic()
        slice_end = min(deadline, now + max(1.0, (deadline - now) / 3.0))
        if _switch_sa(good_n + 1, adj, color, d, D, slice_end, rng):
            good_n += 1
            good_e = [(u, w) for u in range(good_n) for w in adj[u] if u < w]
    return good_n, good_e


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k, annealed (D >= 4).
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for all g.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
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


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Count (representative, vertex) pairs at distance > D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver.
# Phases (fractions of the usable budget): base graphs plus cover growth (to 0.20),
# semidirect voltage annealing for D >= 4 (to 0.40), then switch-annealed vertex
# insertion on the best graph until the deadline.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.88 * time_limit - 2.0)
    deadline = start + total
    t_expand = start + 0.20 * total
    t_anneal = start + 0.40 * total
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
    try:
        if D == 3:
            bases = [(b[0], b[1]) for b in _best_pg(d, 2)]
        elif D >= 4:
            qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
            for q in qs:
                if time.monotonic() >= t_expand:
                    break
                bases.append(_gq_w(q))
        for b in bases:
            consider(b[0], b[1])
    except Exception:
        pass

    # Phase 1: cover growth on the bases, mixed with the best graph.
    try:
        rot = 0
        while bases and time.monotonic() < t_expand:
            if best[0] > 0 and rng.random() < 0.3:
                src = best
            else:
                src = bases[rot % len(bases)]
                rot += 1
            slice_end = min(t_expand, time.monotonic() + 0.08 * total)
            n2, e2 = _grow(src[0], src[1], d, D, slice_end, rng)
            consider(n2, e2)
    except Exception:
        pass

    # Phase 2: voltage-lift annealing over semidirect products, for D >= 4.
    if D >= 4:
        try:
            ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
            while time.monotonic() < t_anneal:
                k = rng.choice(ks)
                base = best[0] // (2 * k)
                G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                res = _anneal(d, D, k, order, mul, rng, t_anneal, iters=1500)
                if res is not None:
                    consider(res[0], res[1])
        except Exception:
            pass

    # Phase 3: switch-annealed vertex insertion on the best graph.
    try:
        if time.monotonic() < deadline and best[0] >= 2:
            n3, e3 = _switch_grow(best[0], best[1], d, D, deadline, rng)
            consider(n3, e3)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
