import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective plane (D = 3) and generalized quadrangle W(q) (D >= 4).
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

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Twin augmentation by packing.
# ----------------------------------------------------------------------------

def _twin_packing(n, adj, slack, rng, deadline):
    cand = [x for x in range(n) if adj[x] and all(slack[w] > 0 for w in adj[x])]
    if not cand:
        return []
    inset = [False] * n
    load = [0] * n

    def take(x):
        inset[x] = True
        for w in adj[x]:
            load[w] += 1

    def drop(x):
        inset[x] = False
        for w in adj[x]:
            load[w] -= 1

    def fill(order):
        for x in order:
            if not inset[x] and all(load[w] < slack[w] for w in adj[x]):
                take(x)

    order = cand[:]
    rng.shuffle(order)
    fill(order)
    best = [x for x in cand if inset[x]]
    while time.monotonic() < deadline:
        chosen = [x for x in cand if inset[x]]
        for x in rng.sample(chosen, min(rng.randint(1, 3), len(chosen))):
            drop(x)
        order = cand[:]
        rng.shuffle(order)
        fill(order)
        cur = sum(1 for x in cand if inset[x])
        if cur > len(best):
            best = [x for x in cand if inset[x]]
        elif cur < len(best) - 2 or rng.random() < 0.01:
            for x in cand:
                if inset[x]:
                    drop(x)
            for x in best:
                take(x)
    return best


def _twin_augment(n, edges, d, rng, deadline):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    slack = [max(0, d - len(a)) for a in adj]
    chosen = _twin_packing(n, adj, slack, rng, deadline)
    E = list(edges)
    N = n
    for x in chosen:
        for w in adj[x]:
            E.append((N, w))
        N += 1
    return N, E


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving) and edge saturation.
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


def _ls_cover(cands, ball, full, d, n, deadline, rng, steps):
    if not cands or full == 0:
        return None
    cur = rng.sample(cands, min(d, len(cands)))

    def cover_of(sel):
        c = 0
        for s in sel:
            c |= ball[s]
        return c

    cur_unc = (full & ~cover_of(cur)).bit_count()
    for _ in range(steps):
        if cur_unc == 0:
            return cur
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(len(cur))
        rest = cur[:i] + cur[i + 1:]
        missing = full & ~cover_of(rest)
        if missing == 0:
            return rest
        while True:
            w = rng.randrange(n)
            if (missing >> w) & 1:
                break
        chosen_set = set(cur)
        opts = [s for s in cands if (ball[s] >> w) & 1 and s not in chosen_set]
        if not opts:
            continue
        new = rng.choice(opts)
        trial = rest + [new]
        u = (full & ~cover_of(trial)).bit_count()
        if u <= cur_unc or rng.random() < 0.02:
            cur = trial
            cur_unc = u
    return cur if cur_unc == 0 else None


def _exact_cover(cands, ball, full, d, budget):
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


def _extend_cover(n, edges, d, D, deadline, rng, restarts, always_random=False):
    if D < 2:
        return n, edges
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
            if D >= 4 and time.monotonic() < deadline:
                chosen = _exact_cover(cands, ball, full, d, 2000)
            if not chosen:
                for attempt in range(restarts):
                    if time.monotonic() >= deadline:
                        break
                    chosen = _greedy_cover(cands, ball, full, d, rng,
                                           always_random or attempt > 0)
                    if chosen:
                        break
            if not chosen and time.monotonic() < deadline:
                chosen = _ls_cover(cands, ball, full, d, n, deadline, rng, 400)
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


def _grow(n, edges, d, D, deadline, rng, restarts=200, always_random=False):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, restarts, always_random)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW CONSTRUCTION: bi-Cayley graphs over a single finite group.
#
# Vertices are (g, 0) and (h, 1) for g, h in G (coded 0..|G|-1 and |G|..2|G|-1).
# For a connection set S (d distinct group elements), (g, 0) ~ (g*s, 1) for s in S.
# Left multiplication by any group element is an automorphism, so the diameter is
# at most D iff every vertex is within D of (e,0) and of (e,1). Two BFS runs
# therefore evaluate a whole candidate, and simulated annealing over S can search
# quickly. Order 2|G| with |G| near the Moore bound / 2 gives large graphs.
# ----------------------------------------------------------------------------

def _divisors_small(G, cap=12):
    return [k for k in range(1, min(cap, G) + 1) if G % k == 0 and G // k >= 2]


def _group_for_order(G, rng):
    """Return (order, mul, inv) for a group of order G: cyclic or a random semidirect Z_m x| Z_k."""
    ks = _divisors_small(G)
    rng.shuffle(ks)
    for k in ks:
        m = G // k
        if k == 1:
            return lib.semidirect_group(m, 1, 1)
        cands = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if cands:
            try:
                return lib.semidirect_group(m, k, rng.choice(cands))
            except ValueError:
                continue
    return None


def _mul_table(G, mul, inv):
    mt = [[mul(x, y) for y in range(G)] for x in range(G)]
    iv = [inv(x) for x in range(G)]
    return mt, iv


def _bc_cost(G, D, S, mt, iv):
    """Number of (source, vertex) pairs at distance > D, sources (e,0) and (e,1)."""
    invS = [iv[s] for s in S]
    total = 0
    for src in (0, G):
        seen = bytearray(2 * G)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    row = mt[u]
                    for s in S:
                        v = G + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = mt[u - G]
                    for si in invS:
                        v = row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += 2 * G - cnt
    return total


def _anneal_bicayley(d, D, G, mt, iv, rng, deadline):
    if d > G:
        return None
    S = rng.sample(range(G), d)
    cur = _bc_cost(G, D, S, mt, iv)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = 0.8 * (0.02 ** frac)
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        new = _bc_cost(G, D, S, mt, iv)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
        else:
            S[i] = old
    return S if cur == 0 else None


def _bicayley_graph(G, mt, S):
    edges = [(g, G + mt[g][s]) for s in S for g in range(G)]
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.15 * time_limit, rng, 200)
            consider(n2, e2)

    if D >= 4:
        # Generalized-quadrangle base plus twin augmentation (strong baseline).
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        twin_deadline = start + 0.3 * time_limit
        for idx, q in enumerate(qs):
            now = time.monotonic()
            if now >= twin_deadline:
                break
            gq = _gq_w(q)
            consider(gq[0], gq[1])
            share = (twin_deadline - now) / (len(qs) - idx)
            tn, te = _twin_augment(gq[0], gq[1], d, rng, time.monotonic() + share)
            consider(tn, te)
            n2, e2 = _grow(tn, te, d, D,
                           min(deadline, time.monotonic() + 0.03 * time_limit),
                           rng, 300, False)
            consider(n2, e2)

    # New search: bi-Cayley graphs over groups of order just above the current record half.
    if D >= 2:
        hi = lib.moore_bound(d, D) // 2
        while time.monotonic() < deadline - 0.05:
            lo = max(d, best_n // 2 + 1)
            if lo > hi:
                break
            G = rng.randint(lo, min(hi, lo + 12))
            remaining = deadline - time.monotonic()
            grp = _group_for_order(G, rng)
            if grp is None:
                continue
            order, mul, inv = grp
            mt, iv = _mul_table(order, mul, inv)
            S = _anneal_bicayley(d, D, order, mt, iv, rng,
                                 time.monotonic() + min(remaining, 4.0))
            if S is not None:
                n, e = _bicayley_graph(order, mt, S)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
