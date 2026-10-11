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
# Graph utilities (set-based adjacency for cheap in-place edits).
# ----------------------------------------------------------------------------

def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _colors(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _balls_sets(n, adj, r):
    """Bitmask of vertices within distance r of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return reach


def _bad(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    reach = _balls_sets(n, adj, D)
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# Twin blow-up with spare-capacity packing (from the parent).
# ----------------------------------------------------------------------------

def _pack(R, cap, n, rng, deadline, iters):
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
    adj = _to_sets(n, edges)
    adjl = [sorted(s) for s in adj]
    color = _colors(n, adjl)
    deg = [len(a) for a in adjl]
    capv = [d - deg[u] for u in range(n)]
    cands = [v for v in range(n)
             if color[v] == side and adjl[v] and all(capv[u] >= 1 for u in adjl[v])]
    if not cands:
        return n, edges
    R = [adjl[v] for v in cands]
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
        for u in adjl[v]:
            new_edges.append((u, nn))
        nn += 1
    return nn, new_edges


# ----------------------------------------------------------------------------
# Cover-based growth (diameter-preserving) and saturation.
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
    adj = _to_sets(n, edges)
    adjl = [sorted(s) for s in adj]
    deg = [len(a) for a in adjl]
    color = _colors(n, adjl)

    while time.monotonic() < deadline:
        ball = _balls_sets(n, adj, D - 1)
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
                adj.append(set())
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].add(v)
                    adj[v].add(s)
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
    adjl = [sorted(s) for s in _to_sets(n, edges)]
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adjl]
    color = _colors(n, adjl)
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
# NEW: forced vertex insertion followed by annealed repair.
#
# Unlike cover growth, a new vertex is inserted even when no full cover exists:
# it joins up to d opposite-side vertices chosen greedily for ball coverage.
# The leftover bad pairs are then repaired by simulated annealing over
# degree-preserving 2-switches (a1-b1, a2-b2 -> a1-b2, a2-b1 with bipartition
# kept) and by adding edges into spare slots. The objective is the number of
# pairs at distance > D. Every move preserves max degree, bipartiteness and the
# vertex set, so a state with objective 0 is a valid graph of one more vertex.
# ----------------------------------------------------------------------------

def _force_add(n, adj, col, d, D, rng):
    """Append one vertex with up to d opposite-side neighbours chosen for coverage."""
    ball = _balls_sets(n, adj, D - 1)
    full = (1 << n) - 1
    c = rng.randrange(2)
    cands = [s for s in range(n) if col[s] == 1 - c and len(adj[s]) < d]
    rng.shuffle(cands)
    covered = 0
    chosen = []
    while cands and len(chosen) < d:
        gains = [(ball[s] & ~covered).bit_count() for s in cands]
        g = max(gains)
        if g == 0:
            break
        idxs = [i for i, x in enumerate(gains) if x == g]
        i = rng.choice(idxs)
        s = cands.pop(i)
        chosen.append(s)
        covered |= ball[s]
        if covered == full:
            break
    v = n
    col.append(c)
    adj.append(set(chosen))
    for s in chosen:
        adj[s].add(v)
    return n + 1


def _anneal(n, adj, col, d, D, deadline, rng, T0=1.0, T1=0.05):
    """Anneal on bad-pair count. Returns (best_bad, best_adj); adj is mutated."""
    side = [[v for v in range(n) if col[v] == c] for c in (0, 1)]
    if not side[0] or not side[1]:
        return _bad(n, adj, D), [set(s) for s in adj]
    B = _bad(n, adj, D)
    if B == 0:
        return 0, [set(s) for s in adj]
    best_B = B
    best_adj = [set(s) for s in adj]
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)

    while B > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        T = T0 * (T1 / T0) ** frac
        if rng.random() < 0.25:
            x = rng.choice(side[0])
            y = rng.choice(side[1])
            if len(adj[x]) >= d or len(adj[y]) >= d or y in adj[x]:
                continue
            adj[x].add(y)
            adj[y].add(x)
            nb = _bad(n, adj, D)
            if nb <= B or rng.random() < math.exp(-(nb - B) / T):
                B = nb
            else:
                adj[x].discard(y)
                adj[y].discard(x)
                continue
        else:
            a = rng.choice(side[0])
            c = rng.choice(side[0])
            if not adj[a] or not adj[c] or a == c:
                continue
            b = rng.choice(tuple(adj[a]))
            e = rng.choice(tuple(adj[c]))
            if b == e or e in adj[a] or b in adj[c]:
                continue
            adj[a].discard(b); adj[b].discard(a)
            adj[c].discard(e); adj[e].discard(c)
            adj[a].add(e); adj[e].add(a)
            adj[c].add(b); adj[b].add(c)
            nb = _bad(n, adj, D)
            if nb <= B or rng.random() < math.exp(-(nb - B) / T):
                B = nb
            else:
                adj[a].discard(e); adj[e].discard(a)
                adj[c].discard(b); adj[b].discard(c)
                adj[a].add(b); adj[b].add(a)
                adj[c].add(e); adj[e].add(c)
                continue
        if B < best_B:
            best_B = B
            best_adj = [set(s) for s in adj]
    return best_B, best_adj


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    expand_deadline = start + 0.35 * time_limit
    hard_deadline = start + 0.90 * time_limit
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

    # Phase 2: forced insertion + annealed repair, repeated while it succeeds.
    if best[0] >= 2:
        cur_n = best[0]
        cur_adj = _to_sets(cur_n, best[1])
        cur_col = _colors(cur_n, [sorted(s) for s in cur_adj])
        slice_len = max(3.0, 0.12 * time_limit)
        while hard_deadline - time.monotonic() > 1.0:
            nadj = [set(s) for s in cur_adj]
            ncol = list(cur_col)
            nn = _force_add(cur_n, nadj, ncol, d, D, rng)
            dl = min(hard_deadline, time.monotonic() + slice_len)
            B, fadj = _anneal(nn, nadj, ncol, d, D, dl, rng)
            if B == 0:
                edges = [(u, v) for u in range(nn) for v in fadj[u] if u < v]
                if lib.is_valid(nn, edges, d, D):
                    cur_n, cur_adj, cur_col = nn, fadj, ncol
                    if nn > best[0]:
                        best = (nn, edges)
                    continue
            # Failed attempt: keep the current state and try another insertion.

    return best
