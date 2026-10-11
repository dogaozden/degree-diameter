import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Basic graph helpers.
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
# Base constructions.
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q), q the largest prime power with q + 1 <= d (D = 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the symplectic generalized quadrangle W(q)."""
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


def _gq_base(d):
    """W(q) with q the largest prime power <= min(d - 1, 9); degree q + 1 <= d (D >= 4)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Growth by covering and edge saturation (parent-style expansion).
# ----------------------------------------------------------------------------

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
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    attempts_max = 200

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(attempts_max):
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


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(12):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


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


def _expansion_loop(d, D, seed, deadline, bases, consider, st):
    if not bases:
        return
    target = lib._moore_bound(d, D)
    attempt = 0
    while time.monotonic() < deadline and st["best"][0] < target:
        attempt += 1
        arng = random.Random(seed * 1000003 + attempt)
        if arng.random() < 0.35:
            src = st["best"]
        else:
            src = bases[attempt % len(bases)]
        n2, e2 = _expand(src[0], src[1], d, D, deadline, arng)
        e2 = _saturate_edges(n2, e2, d, arng)
        consider(n2, e2)


# ----------------------------------------------------------------------------
# NEW (bold): vertex-deletion search on a larger generalized quadrangle.
#
# W(qd) with qd = smallest prime power >= d is (qd+1)-regular with diameter 4.
# Deleting vertices lowers degrees to <= d. We anneal over the kept set,
# maximising  kept - LAM * (bad pairs + degree excess).  Only cost-0 states
# (valid graphs) are reported, through consider(), which re-verifies them.
# ----------------------------------------------------------------------------

def _delete_search(qd, d, D, rng, deadline, consider):
    N, E = _gq_w(qd)
    adj = _adjacency(N, E)
    alive = [True] * N
    deg = [len(a) for a in adj]   # deg[v] = number of ALIVE neighbours of v
    kept = N
    LAM = 0.5

    def kill(u):
        nonlocal kept
        alive[u] = False
        kept -= 1
        for w in adj[u]:
            deg[w] -= 1

    def revive(u):
        nonlocal kept
        alive[u] = True
        kept += 1
        for w in adj[u]:
            deg[w] += 1

    # Initial repair: remove high-degree neighbours until max degree <= d.
    while True:
        over = [v for v in range(N) if alive[v] and deg[v] > d]
        if not over:
            break
        v = rng.choice(over)
        u = max((x for x in adj[v] if alive[x]), key=lambda x: (deg[x], rng.random()))
        kill(u)

    def cost():
        al = [v for v in range(N) if alive[v]]
        exc = 0
        for v in al:
            if deg[v] > d:
                exc += deg[v] - d
        reach = [0] * N
        for v in al:
            reach[v] = 1 << v
        for _ in range(D):
            new = [0] * N
            for v in al:
                x = reach[v]
                for u in adj[v]:
                    if alive[u]:
                        x |= reach[u]
                new[v] = x
            reach = new
        K = len(al)
        bad = sum(K - reach[v].bit_count() for v in al) // 2
        return bad, exc

    def report():
        e = [(u, v) for v in range(N) if alive[v] for u in adj[v] if alive[u] and u < v]
        n_, e_ = lib.relabel(e)
        consider(n_, e_)

    bad, exc = cost()
    cur = kept - LAM * (bad + exc)
    best_k = 0
    if bad == 0 and exc == 0 and kept >= 2:
        best_k = kept
        report()

    T0, T1 = 2.0, 0.05
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while time.monotonic() < deadline:
        frac = min(1.0, (time.monotonic() - t0) / span)
        T = T0 * (1.0 - frac) + T1 * frac
        u = rng.randrange(N)
        if rng.random() < 0.5:
            if not alive[u] or kept <= 2:
                continue
            kill(u)
            kind = "k"
        else:
            if alive[u]:
                continue
            revive(u)
            kind = "r"

        b2, e2 = cost()
        new = kept - LAM * (b2 + e2)
        if new >= cur or rng.random() < math.exp((new - cur) / max(T, 1e-6)):
            cur = new
            bad, exc = b2, e2
            if bad == 0 and exc == 0 and kept > best_k and kept >= 2:
                best_k = kept
                report()
        else:
            if kind == "k":
                revive(u)
            else:
                kill(u)


# ----------------------------------------------------------------------------
# Search orchestration.
# ----------------------------------------------------------------------------

def _run(d, D, seed, start, total, deadline, rng, consider, st):
    if D == 2:
        return
    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return

    if D == 3:
        b = _pg_base(d)
        if b is None:
            return
        consider(b[0], b[1])
        return

    # D >= 4
    base = _gq_base(d)
    if base is not None:
        consider(base[0], base[1])
    if st["best"][0] >= lib._moore_bound(d, D):
        return

    qd = next((q for q in range(max(d, 2), 12) if lib.is_prime_power(q)), None)
    bases = [base] if base is not None else []

    _expansion_loop(d, D, seed, start + 0.25 * total, bases, consider, st)

    if qd is not None and time.monotonic() < start + 0.85 * total:
        _delete_search(qd, d, D, rng, start + 0.85 * total, consider)

    if st["best"][0] < lib._moore_bound(d, D):
        _expansion_loop(d, D, seed, deadline, [st["best"]], consider, st)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.8 * time_limit
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    st = {"best": lib.haar_graph(d, range(d))}  # K_{d,d}: valid fallback for D >= 2

    def consider(n, e):
        if n > st["best"][0] and lib.is_valid(n, e, d, D):
            st["best"] = (n, e)

    if st["best"][0] < lib._moore_bound(d, D):
        try:
            _run(d, D, seed, start, total, deadline, rng, consider, st)
        except Exception:
            pass

    n, e = st["best"]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
