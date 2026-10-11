import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases (unchanged from the parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


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


def _extend_cover(n, edges, d, D, deadline, rng=None):
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
            for attempt in range(200):
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


def _duplicate_twins(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# NEW: bi-Cayley (Haar-type) search with bitset reachability.
#
# A Haar graph over Z_m with connection set S (|S| = d) has a_i ~ b_{i+s}.
# It is d-regular and bipartite, and it is vertex-transitive on each side.
# By the shift automorphisms, diameter <= D holds iff a_0 reaches all of the
# A side and all of the B side within D steps, and b_0 does the same. So the
# cost is the total number of unreached (source, target) pairs from a_0 and
# b_0, which is exact and cheap: each BFS is a few big-int rotations per level.
#
# Note: this family overlaps the cyclic voltage lifts of the parent; what is
# new here is the exact bitset objective and the annealing over the
# connection set itself, with the m sweep handled by the phase driver.
# ----------------------------------------------------------------------------

def _rot(X, s, m, full):
    """Cyclic rotation of an m-bit set: bit i moves to bit (i + s) mod m."""
    return ((X << s) | (X >> (m - s))) & full


def _haar_cost(m, S, Sneg, D):
    """Sum of unreached counts from a_0 and b_0 (zero iff the Haar graph has diameter <= D)."""
    full = (1 << m) - 1
    total = 0
    for start_side in (0, 1):
        if start_side == 0:
            fa, fb, sa, sb = 1, 0, 1, 0
        else:
            fa, fb, sa, sb = 0, 1, 0, 1
        for _ in range(D):
            na = 0
            for t in Sneg:
                na |= _rot(fb, t, m, full)
            na &= ~sa & full
            sa |= na
            nb = 0
            for s in S:
                nb |= _rot(fa, s, m, full)
            nb &= ~sb & full
            sb |= nb
            fa, fb = na, nb
            if not (fa or fb):
                break
        total += sa.bit_count() + sb.bit_count()
    return 4 * m - total


def _haar_anneal(m, d, D, rng, deadline):
    """Anneal a d-element residue set S in Z_m until the Haar graph H(m, S) has diameter <= D."""
    if m < d or m < 2:
        return None
    S = rng.sample(range(m), d)
    Sneg = [(-s) % m for s in S]
    cur = _haar_cost(m, S, Sneg, D)
    temp = 1.0
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        new = rng.randrange(m)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        Sneg[i] = (-new) % m
        c = _haar_cost(m, S, Sneg, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            S[i] = old
            Sneg[i] = (-old) % m
        temp = max(0.05, temp * 0.999)
    return list(S) if cur == 0 else None


def _haar_phase(d, D, get_best_n, deadline, rng, consider):
    """Sweep m upward from the current best order, annealing Haar connection sets."""
    m = get_best_n() // 2 + 1
    while time.monotonic() < deadline:
        slice_end = min(deadline, time.monotonic() + 3.0)
        S = _haar_anneal(m, d, D, rng, slice_end)
        if S is None:
            m = max(m, get_best_n() // 2 + 1)
            continue
        n, e = lib.haar_graph(m, S)
        consider(n, e)
        n2, e2 = _grow(n, e, d, D, deadline, rng)
        consider(n2, e2)
        m = max(m + 1, get_best_n() // 2 + 1)


# ----------------------------------------------------------------------------
# Spare-slot annealing (unchanged from the parent).
# ----------------------------------------------------------------------------

def _pick_spare_pair(adj, color, d, rng):
    n = len(adj)
    spare = [v for v in range(n) if len(adj[v]) < d]
    if len(spare) < 2:
        return None
    for _ in range(30):
        a = rng.choice(spare)
        opp = [w for w in spare
               if color[w] != color[a] and w not in adj[a] and len(adj[w]) < d]
        if opp:
            return a, rng.choice(opp)
    return None


def _spare_anneal(n, edges, d, D, rng, deadline, consider, temp0=0.5):
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    cur = _cost(adj, D)
    temp = temp0
    while time.monotonic() < deadline:
        if cur == 0:
            e = [(u, v) for u in range(n) for v in adj[u] if u < v]
            consider(n, e)
            n2, e2 = _grow(n, e, d, D, deadline, rng)
            consider(n2, e2)
            n = n2
            adj = _to_sets(n, e2)
            color = _bipartition(n, adj)
            cur = _cost(adj, D)
            if cur == 0:
                temp = temp0
                u = rng.randrange(n)
                if adj[u]:
                    v = rng.choice(tuple(adj[u]))
                    adj[u].discard(v)
                    adj[v].discard(u)
                    cur = _cost(adj, D)
                continue
        mv = rng.random()
        if mv < 0.6:
            pair = _pick_spare_pair(adj, color, d, rng)
            if pair is None:
                mv = 1.0
            else:
                a, b = pair
                adj[a].add(b)
                adj[b].add(a)
                new = _cost(adj, D)
                if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                    cur = new
                else:
                    adj[a].discard(b)
                    adj[b].discard(a)
                temp = max(0.05, temp * 0.9995)
                continue
        cand_u = [x for x in range(n) if adj[x]]
        if not cand_u:
            break
        u = rng.choice(cand_u)
        v = rng.choice(tuple(adj[u]))
        adj[u].discard(v)
        adj[v].discard(u)
        w = None
        spare_opp = [x for x in range(n)
                     if color[x] != color[u] and x != v and x not in adj[u]
                     and len(adj[x]) < d]
        if spare_opp:
            w = rng.choice(spare_opp)
            adj[u].add(w)
            adj[w].add(u)
        new = _cost(adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
        else:
            if w is not None:
                adj[u].discard(w)
                adj[w].discard(u)
            adj[u].add(v)
            adj[v].add(u)
        temp = max(0.05, temp * 0.9995)


def _spare_phase(d, D, get_best, deadline, rng, consider):
    while time.monotonic() < deadline:
        bn, be = get_best()
        slice_end = min(deadline, time.monotonic() + 4.0)
        _spare_anneal(bn, be, d, D, rng, slice_end, consider)


# ----------------------------------------------------------------------------
# Bipartite voltage lifts over small groups (unchanged from the parent).
# ----------------------------------------------------------------------------

def _group_options(G):
    """(M, k, r) triples describing groups of order G: cyclic plus Z_M x|_r Z_k with M*k = G."""
    opts = [(G, 1, 1)]
    for k in range(2, G + 1):
        if G % k:
            continue
        M = G // k
        if M < 2:
            continue
        for r in range(1, M):
            if math.gcd(r, M) == 1 and pow(r, k, M) == 1 % M:
                opts.append((M, k, r))
    return opts


def _random_darts(s, d, G, rng):
    a = [i for i in range(s) for _ in range(d)]
    b = list(a)
    rng.shuffle(b)
    return [(i, s + j, rng.randrange(G)) for i, j in zip(a, b)]


def _lift_search(d, D, s, G, mul, rng, deadline, darts=None, temp=0.6):
    if darts is None:
        darts = _random_darts(s, d, G, rng)
    n, e = lib.group_lift(2 * s, darts, G, mul)
    cur = _cost(_to_sets(n, e), D)
    while cur > 0:
        if time.monotonic() > deadline:
            return None, darts, temp
        old = list(darts)
        k = len(darts)
        if k >= 2 and rng.random() < 0.5:
            p = rng.randrange(k)
            q = rng.randrange(k)
            if p == q:
                continue
            ip, jp, gp = darts[p]
            iq, jq, gq = darts[q]
            darts[p] = (ip, jq, gp)
            darts[q] = (iq, jp, gq)
        else:
            p = rng.randrange(k)
            i, j, _ = darts[p]
            darts[p] = (i, j, rng.randrange(G))
        n2, e2 = lib.group_lift(2 * s, darts, G, mul)
        new = _cost(_to_sets(n2, e2), D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
            n, e = n2, e2
        else:
            darts = old
        temp = max(0.05, temp * 0.999)
    return (n, e), darts, temp


def _lift_phase(d, D, get_best, deadline, rng, consider):
    states = {}
    while time.monotonic() < deadline:
        best_n = get_best()
        states = {key: v for key, v in states.items() if 2 * key[0] * key[1] > best_n}
        if states and rng.random() < 0.7:
            key = rng.choice(list(states))
            darts, temp = states.pop(key)
            s, G, M, k, r = key
        else:
            darts, temp = None, 0.6
            s = rng.choice((1, 2, 2, 3, 3, 4, 5, 6))
            G_min = best_n // (2 * s) + 1
            G = G_min + rng.randrange(4)
            opts = _group_options(G)
            if not opts:
                continue
            M, k, r = rng.choice(opts)
            key = (s, G, M, k, r)
        try:
            _, mul, _ = lib.semidirect_group(M, k, r)
        except ValueError:
            continue
        slice_end = min(deadline, time.monotonic() + 3.0)
        res, darts, temp = _lift_search(d, D, s, G, mul, rng, slice_end, darts, temp)
        if res is None:
            states[key] = (darts, temp)
            if len(states) > 40:
                states.pop(next(iter(states)))
            continue
        n, e = res
        consider(n, e)
        n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, deadline, rng)
        consider(n2, e2)


# ----------------------------------------------------------------------------
# Large-neighbourhood search and pruning (unchanged from the parent).
# ----------------------------------------------------------------------------

def _fill(adj, color, d, rng):
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _lns(n, edges, d, D, deadline, rng, consider):
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


def _prune_redundant(n, edges, D, rng, deadline, max_tests):
    adj = _to_sets(n, edges)
    cand = list(edges)
    rng.shuffle(cand)
    tests = 0
    for u, v in cand:
        if tests >= max_tests or time.monotonic() > deadline:
            break
        if v not in adj[u]:
            continue
        tests += 1
        adj[u].discard(v)
        adj[v].discard(u)
        if _cost(adj, D) != 0:
            adj[u].add(v)
            adj[v].add(u)
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


def _prune_regrow(n, edges, d, D, deadline, rng, consider):
    best_n, best_e = n, list(edges)
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        pe = _prune_redundant(cur_n, cur_e, D, rng, deadline, 160)
        n2, e2 = _grow(cur_n, pe, d, D, deadline, rng)
        consider(n2, e2)
        if n2 > best_n:
            best_n, best_e = n2, list(e2)
        if n2 >= cur_n - 1:
            cur_n, cur_e = n2, list(e2)
        elif n2 < best_n - 2 or rng.random() < 0.3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Driver. Budget T = 0.8 * time_limit, split into phases:
#   A  structured base (W(q) or PG(2,q)) grown, then twin/grow trials
#   H  NEW: bi-Cayley (Haar) connection-set annealing with bitset cost
#   S  spare-slot annealing from the best valid graph
#   L  voltage lifts over small groups, annealed to diameter <= D, then grown
#   C  LNS from the best valid graph
#   D  redundant-edge pruning and regrowth
# Every kept graph passes lib.is_valid. The Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.8 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase A: structured base, grown; then twin/grow trials.
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    base_n, base_e = best_n, list(best_e)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        base_n, base_e = n0, list(e0)
        n1, e1 = _grow(n0, e0, d, D, at(0.10), rng)
        consider(n1, e1)
    if D >= 2:
        trial_end = at(0.20)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase H: bi-Cayley (Haar) connection-set annealing, sweeping m upward.
    if D >= 3 and d >= 3 and time.monotonic() < at(0.35):
        _haar_phase(d, D, lambda: best_n, at(0.35), rng, consider)

    # Phase S: spare-slot annealing from the best valid graph so far.
    if D >= 3 and time.monotonic() < at(0.45):
        _spare_phase(d, D, lambda: (best_n, list(best_e)), at(0.45), rng, consider)

    # Phase L: voltage lifts over small groups (parked runs are resumed).
    if D >= 2 and time.monotonic() < at(0.62):
        _lift_phase(d, D, lambda: best_n, at(0.62), rng, consider)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase C: LNS from the best valid graph of any construction.
    if D >= 2 and time.monotonic() < at(0.85):
        _lns(best_n, best_e, d, D, at(0.85), rng, consider)

    # Phase D: prune redundant edges and regrow from the best graph.
    if D >= 2 and time.monotonic() < at(0.97):
        _prune_regrow(best_n, best_e, d, D, at(0.97), rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
