import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: block-packed orbit voltage lifts.
#
# Base graph: k A-vertices and k B-vertices, joined by d perfect matchings
# sigma_0..sigma_{d-1} (so every base vertex has degree d). Each base dart
# (A_i, B_{sigma_t(i)}) carries a voltage V[t][i] in Z_m. The lift has vertices
# A_{i,x}, B_{j,y} (x, y in Z_m), with A_{i,x} ~ B_{sigma_t(i), x+V[t][i]}.
# It is d-regular and bipartite. The lift is simple iff for each i the d pairs
# (sigma_t(i), V[t][i]) are distinct.
#
# Diameter check, compressed by the Z_m symmetry: from each of the 2k base
# sources (position 0), the reach set of every base vertex is a subset of Z_m.
# All 2k sources are packed into one big integer per base vertex, with one
# m-bit block per source. A rotation by a shift in Z_m acts on every block at
# once through two precomputed masks (lo[a], hi[a]). The cost is the number of
# (vertex, source) pairs not reached within D steps. Cost 0 iff diameter <= D.
#
# k = 1 is exactly a cyclic Haar graph. Larger k gives a richer search space.
# Simulated annealing moves voltages and swaps entries of the matchings.
# ----------------------------------------------------------------------------

def _rot_masks(m, FULL, blocks):
    """lo[a], hi[a]: bits of each m-bit block whose position x satisfies x + a < m (lo) or not (hi)."""
    P = [sum(((1 << c) - 1) << (s * m) for s in range(blocks)) for c in range(m + 1)]
    lo = [P[m - a] for a in range(m)]
    hi = [FULL ^ P[m - a] for a in range(m)]
    return lo, hi


def _random_config(k, m, d, rng):
    """Random matchings sig[t] (permutations of range(k)) and voltages V[t][i] with distinct (sig, V) per row."""
    sig = [rng.sample(range(k), k) for _ in range(d)]
    V = [[0] * k for _ in range(d)]
    for i in range(k):
        used = set()
        for t in range(d):
            j = sig[t][i]
            opts = [a for a in range(m) if (j, a) not in used]
            a = rng.choice(opts)
            used.add((j, a))
            V[t][i] = a
    return sig, V


def _ok_row(i, sig, V, d):
    """True if the d pairs (sig[t][i], V[t][i]) are distinct (lift stays simple)."""
    seen = set()
    for t in range(d):
        p = (sig[t][i], V[t][i])
        if p in seen:
            return False
        seen.add(p)
    return True


def _nbrs(k, d, sig, V):
    A_nb = [[(sig[t][i], V[t][i]) for t in range(d)] for i in range(k)]
    B_nb = [[] for _ in range(k)]
    for t in range(d):
        for i in range(k):
            B_nb[sig[t][i]].append((i, V[t][i]))
    return A_nb, B_nb


def _orbit_cost(k, m, D, A_nb, B_nb, lo, hi, FB):
    """Number of (vertex, source) pairs at distance > D, computed on packed blocks."""
    SA = [1 << (i * m) for i in range(k)]          # source A_i is block i
    SB = [1 << ((k + j) * m) for j in range(k)]    # source B_j is block k+j
    for _ in range(D):
        nA = []
        for i in range(k):
            x = SA[i]
            for j, a in A_nb[i]:
                r = (m - a) % m
                y = SB[j]
                x |= ((y & lo[r]) << r) | ((y & hi[r]) >> (m - r))
            nA.append(x)
        nB = []
        for j in range(k):
            y = SB[j]
            for i, a in B_nb[j]:
                x = SA[i]
                y |= ((x & lo[a]) << a) | ((x & hi[a]) >> (m - a))
            nB.append(y)
        SA, SB = nA, nB
    c = 0
    for x in SA:
        c += FB - x.bit_count()
    for y in SB:
        c += FB - y.bit_count()
    return c


def _orbit_edges(k, m, d, sig, V):
    edges = []
    off = k * m
    for t in range(d):
        for i in range(k):
            j = sig[t][i]
            a = V[t][i]
            for x in range(m):
                edges.append((i * m + x, off + j * m + (x + a) % m))
    return 2 * k * m, edges


def _orbit_search(k, m, d, D, deadline, rng):
    """Anneal matchings and voltages for a k-base lift over Z_m. Returns (n, edges) or None."""
    blocks = 2 * k
    FB = blocks * m
    FULL = (1 << FB) - 1
    lo, hi = _rot_masks(m, FULL, blocks)
    sig, V = _random_config(k, m, d, rng)

    def cost(sg, vv):
        A_nb, B_nb = _nbrs(k, d, sg, vv)
        return _orbit_cost(k, m, D, A_nb, B_nb, lo, hi, FB)

    c = cost(sig, V)
    T = 1.0
    it = 0
    while c > 0:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            return None
        if it % 20000 == 0:
            T = 1.0  # reheat
        if k == 1 or rng.random() < 0.6:
            t = rng.randrange(d)
            i = rng.randrange(k)
            old = V[t][i]
            nv = rng.randrange(m)
            if nv == old:
                continue
            V[t][i] = nv
            if not _ok_row(i, sig, V, d):
                V[t][i] = old
                continue
            c2 = cost(sig, V)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                c = c2
            else:
                V[t][i] = old
        else:
            t = rng.randrange(d)
            i, i2 = rng.sample(range(k), 2)
            row = sig[t]
            row[i], row[i2] = row[i2], row[i]
            if not (_ok_row(i, sig, V, d) and _ok_row(i2, sig, V, d)):
                row[i], row[i2] = row[i2], row[i]
                continue
            c2 = cost(sig, V)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                c = c2
            else:
                row[i], row[i2] = row[i2], row[i]
        T = max(0.1, T * 0.9995)
    return _orbit_edges(k, m, d, sig, V)


def _orbit_phase(d, D, moore, best_n, deadline, rng, per):
    """Ladder over (k, m): for each base size k, take the smallest m that beats the best order."""
    ks = [1, 2, 3, 4, 5, 6]
    mk = {k: d for k in ks}
    fails = {k: 0 for k in ks}
    active = list(ks)
    result = None
    while active and time.monotonic() < deadline:
        for k in list(active):
            if time.monotonic() >= deadline:
                break
            need = best_n // (2 * k) + 1
            m = max(mk[k], need, d)
            if 2 * k * m > moore:
                active.remove(k)
                continue
            mk[k] = m
            cfg_deadline = min(deadline, time.monotonic() + per)
            res = _orbit_search(k, m, d, D, cfg_deadline, rng)
            if res is not None:
                n, edges = res
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best_n = n
                    result = (n, edges)
                    mk[k] = m + 1
            else:
                fails[k] += 1
                if fails[k] >= 8:
                    active.remove(k)
    return result


# ----------------------------------------------------------------------------
# Legacy pipeline (previous parent): PG(2,q) / W(q) bases, twin packing, cover
# growth, local search and annealing. Kept as a fallback and for the remaining time.
# ----------------------------------------------------------------------------

def _best_pg(d, count=1):
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


def _remove_vertex(n, edges, x):
    last = n - 1

    def m(v):
        return x if v == last else v

    new = [(m(u), m(v)) for u, v in edges if u != x and v != x]
    return n - 1, new


def _add_one(n, edges, d, D, rng):
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
    while time.monotonic() < deadline:
        r = _add_one(n, edges, d, D, rng)
        if r is None:
            break
        n, edges = r
    edges = _saturate_edges(n, edges, d, rng)
    return n, edges


def _ils(n, edges, d, D, deadline, rng, holder):
    cn, ce = n, list(edges)
    while time.monotonic() < deadline:
        if holder[0][0] > cn and rng.random() < 0.002:
            cn, ce = holder[0][0], list(holder[0][1])
        x = rng.randrange(cn)
        rn, re = _remove_vertex(cn, ce, x)
        if rn <= 0:
            continue
        if not lib.within_diameter(rn, re, D):
            re = _saturate_edges(rn, re, d, rng)
            if not lib.within_diameter(rn, re, D):
                continue
        rn, re = _fill(rn, re, d, D, rng, deadline)
        if rn >= cn or (rn == cn - 1 and rng.random() < 0.05):
            cn, ce = rn, re
            if rn > holder[0][0] and lib.is_valid(rn, re, d, D):
                holder[0] = (rn, re)
    return


def _sets_from_edges(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _bad_sets(N, adj, D):
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _apply(adj, op):
    kind, a, b = op
    if kind == 'add':
        adj[a].add(b)
        adj[b].add(a)
    else:
        adj[a].discard(b)
        adj[b].discard(a)


def _undo(adj, op):
    kind, a, b = op
    if kind == 'add':
        adj[a].discard(b)
        adj[b].discard(a)
    else:
        adj[a].add(b)
        adj[b].add(a)


def _greedy_partial(cands, ball, d):
    pool = list(cands)
    covered = 0
    chosen = []
    while pool and len(chosen) < d:
        best_i = max(range(len(pool)),
                     key=lambda i: (ball[pool[i]] & ~covered).bit_count())
        s = pool.pop(best_i)
        chosen.append(s)
        covered |= ball[s]
    return chosen


def _anneal_add(n, edges, d, D, deadline, rng, T0=0.8):
    if n < 2 or not edges:
        return None
    adj_lists = _adjacency(n, edges)
    color = _bipartition(n, adj_lists)
    deg = [len(a) for a in adj_lists]
    c = rng.randrange(2)
    opp = [x for x in range(n) if color[x] == 1 - c]
    if not opp:
        return None

    ball = _balls_radius(n, adj_lists, D - 1)
    cands = [s for s in opp if deg[s] < d]
    rng.shuffle(cands)
    init = _greedy_partial(cands, ball, d) if cands else []

    adj = _sets_from_edges(n, edges)
    v = n
    N = n + 1
    adj.append(set())
    for s in init:
        adj[v].add(s)
        adj[s].add(v)

    cur = _bad_sets(N, adj, D)
    it = 0
    while time.monotonic() < deadline:
        if cur == 0:
            new_edges = [(a, b) for a in range(N) for b in adj[a] if a < b]
            if lib.is_valid(N, new_edges, d, D):
                return N, new_edges
            return None
        it += 1
        t = opp[rng.randrange(len(opp))]
        if t in adj[v]:
            continue
        ops = []
        if len(adj[v]) >= d:
            s = rng.choice(tuple(adj[v]))
            ops.append(('del', v, s))
        if len(adj[t]) >= d:
            u = rng.choice(tuple(adj[t]))
            ops.append(('del', t, u))
        ops.append(('add', v, t))
        for op in ops:
            _apply(adj, op)
        new = _bad_sets(N, adj, D)
        delta = new - cur
        T = max(0.05, T0 * (0.999 ** it))
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            for op in reversed(ops):
                _undo(adj, op)
    return None


def _legacy_build(d, D, seed, time_limit):
    start = time.monotonic()
    expand_deadline = start + 0.35 * time_limit
    ils_deadline = start + 0.70 * time_limit
    anneal_deadline = start + 0.88 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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

    if time.monotonic() < ils_deadline and best[0] >= 2:
        holder = [best]
        _ils(best[0], best[1], d, D, ils_deadline, rng, holder)
        if holder[0][0] > best[0] and lib.is_valid(holder[0][0], holder[0][1], d, D):
            best = holder[0]

    while best[0] >= 2 and time.monotonic() < anneal_deadline:
        slice_end = min(anneal_deadline, time.monotonic() + 4.0)
        res = _anneal_add(best[0], best[1], d, D, slice_end, rng)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    return best


# ----------------------------------------------------------------------------
# Driver: orbit voltage-lift search first, then the legacy pipeline with the
# remaining time. Every candidate is checked with lib.is_valid before it can
# replace the best. The K_{d,d} fallback is valid for D >= 2.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Phase 1: block-packed orbit lifts (k base vertices per side, Z_m voltages).
    per = max(0.3, 0.04 * T)
    try:
        r = _orbit_phase(d, D, moore, best[0], start + 0.45 * T, rng, per)
    except Exception:
        r = None
    if r is not None:
        consider(r[0], r[1])
    if best[0] >= moore:
        return best

    # Phase 2: legacy pipeline with the remaining time (it scales its own deadlines).
    remaining = start + 0.88 * T - time.monotonic()
    if remaining > 2.0:
        try:
            leg = _legacy_build(d, D, seed, remaining / 0.9)
        except Exception:
            leg = None
        if leg is not None:
            consider(leg[0], leg[1])

    return best
