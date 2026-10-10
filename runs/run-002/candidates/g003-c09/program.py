import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000        # hard cap on vertex count
ITERS = 2000        # annealing iterations per attempt
RETRIES = 2         # annealing attempts per candidate lift size
ATT_SLICE = 0.7     # seconds allowed for one annealing attempt
GQ_Q_MAX = 9        # largest q for which W(q) is built
POST_LIFTS = 3      # number of largest lifts that get growth post-processing
ILS_STEP = 0.5      # seconds allowed for one remove-and-regrow step


# ---------------------------------------------------------------- shared helpers

def _colour(n, edges):
    """Proper 2-colouring (0/1 per vertex) of a bipartite graph, component by component."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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


def _deg(n, edges):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return deg


def _cover(balls, cand, target, budget, rng):
    """Greedy set cover of `target` bitmask by balls of at most `budget` candidates.

    Returns the chosen list, or None if the cover fails.
    """
    cand = list(cand)
    rng.shuffle(cand)
    covered = 0
    chosen = []
    while (target & ~covered) and len(chosen) < budget and cand:
        best_u, best_g = -1, 0
        for u in cand:
            g = (balls[u] & ~covered & target).bit_count()
            if g > best_g:
                best_u, best_g = u, g
        if best_u < 0:
            break
        chosen.append(best_u)
        covered |= balls[best_u]
        cand.remove(best_u)
    if target & ~covered:
        return None
    return chosen


def _saturate(n, edges, d, rng, deadline):
    """Join deficient opposite-colour vertices. Preserves validity and bipartiteness."""
    edges = list(edges)
    color = _colour(n, edges)
    deg = _deg(n, edges)
    existing = set((min(u, v), max(u, v)) for u, v in edges)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    rng.shuffle(left)
    rng.shuffle(right)
    for a in left:
        if time.monotonic() > deadline:
            break
        for b in right:
            if deg[a] >= d:
                break
            if deg[b] < d and (min(a, b), max(a, b)) not in existing:
                edges.append((a, b))
                existing.add((min(a, b), max(a, b)))
                deg[a] += 1
                deg[b] += 1
    return edges


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add single vertices whose neighbourhoods cover everything within D-1."""
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _colour(n, edges)
    deg = _deg(n, edges)
    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            chosen = _cover(balls, cand, full, d, rng)
            if chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _pair_extend(n, edges, d, D, rng, deadline):
    """Add two adjacent new vertices x (colour c) and y (colour 1-c) at once."""
    edges = list(edges)
    if D < 3 or n == 0 or d < 2:
        return n, edges
    color = _colour(n, edges)
    deg = _deg(n, edges)
    while time.monotonic() < deadline:
        full = (1 << n) - 1
        b1 = lib._balls(n, edges, D - 1)
        b2 = lib._balls(n, edges, D - 2)
        placed = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            side_other = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            side_c = [u for u in range(n) if color[u] == c and deg[u] < d]
            N = _cover(b1, side_other, full, d - 1, rng)
            if not N:
                continue
            b2N = 0
            for u in N:
                b2N |= b2[u]
            M = _cover(b1, side_c, full & ~b2N, d - 1, rng)
            if M is None:
                continue
            x, y = n, n + 1
            n += 2
            color.append(c)
            color.append(1 - c)
            deg.append(len(N) + 1)
            deg.append(len(M) + 1)
            for u in N:
                edges.append((u, x))
                deg[u] += 1
            for u in M:
                edges.append((u, y))
                deg[u] += 1
            edges.append((x, y))
            placed = True
            break
        if not placed:
            break
    return n, edges


def _grow(n, edges, d, D, rng, deadline):
    """Alternate saturation, single and paired extension until nothing changes."""
    edges = list(edges)
    for _ in range(50):
        if time.monotonic() >= deadline:
            break
        prev = n
        edges = _saturate(n, edges, d, rng, deadline)
        n, edges = _extend(n, edges, d, D, rng, deadline)
        n, edges = _pair_extend(n, edges, d, D, rng, deadline)
        if n == prev:
            break
    return n, edges


def _remove_vertex(n, edges, v):
    out = []
    for a, b in edges:
        if a == v or b == v:
            continue
        out.append((a - 1 if a > v else a, b - 1 if b > v else b))
    return n - 1, out


def _ils(n, edges, d, D, rng, end):
    """Iterated local search: delete a random vertex, regrow, keep if valid and not smaller."""
    cur = (n, list(edges))
    best = cur
    while time.monotonic() < end:
        n0, e0 = cur
        if n0 < 4:
            break
        v = rng.randrange(n0)
        m, e1 = _remove_vertex(n0, e0, v)
        m, e2 = _grow(m, e1, d, D, rng, min(end, time.monotonic() + ILS_STEP))
        if m >= n0 and lib.is_valid(m, e2, d, D):
            cur = (m, e2)
            if m > best[0]:
                best = (m, e2)
    return best


# ---------------------------------------------------------------- base graphs

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


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
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m with diameter <= D."""
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


# ---------------------------------------------------------------- group lifts

def _make_group(m, k, r):
    """Group Z_m x|_r Z_k as (m, k, powers of r); element (a, b) is coded a*k+b."""
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    return (m, k, pw)


def _pick_group(m, k, rng):
    r = 1
    if k > 1 and m >= 3 and rng.random() < 0.7:
        cands = [x for x in range(2, m) if math.gcd(x, m) == 1 and pow(x, k, m) == 1]
        if cands:
            r = rng.choice(cands)
    return _make_group(m, k, r)


def _mulvec(grp, xs, g):
    """Vectorised right multiplication x * g over an array of element codes."""
    m, k, pw = grp
    c, dd = divmod(g, k)
    a = xs // k
    b = xs % k
    return ((a + pw[b] * c) % m) * k + (b + dd) % k


def _set_dart(nbr, s, G, grp, xs, P, V, kk, i):
    """Write the edges of dart (kk, i): left block i joins right block P[kk,i] with voltage V[kk,i]."""
    j = int(P[kk, i])
    F = _mulvec(grp, xs, int(V[kk, i]))
    inv = np.empty(G, dtype=np.int64)
    inv[F] = xs
    nbr[i * G:(i + 1) * G, kk] = s * G + j * G + F
    nbr[(s + j) * G:(s + j + 1) * G, kk] = i * G + inv


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs not within distance D. Zero iff the lift is valid."""
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M = R.copy()
        for kk in range(nbr.shape[1]):
            M |= R[:, nbr[:, kk]]
        if np.array_equal(M, R):
            break
        R = M
    return int(S * n - np.count_nonzero(R))


def _anneal(s, grp, d, D, rng, deadline, iters):
    """Anneal permutations and voltages of a d-regular bipartite base lifted over grp.

    Returns (nbr, G) with zero cost, or None.
    """
    G = grp[0] * grp[1]
    xs = np.arange(G, dtype=np.int64)
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    V = np.array([[rng.randrange(G) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    nbr = np.empty((2 * s * G, d), dtype=np.int64)
    for kk in range(d):
        for i in range(s):
            _set_dart(nbr, s, G, grp, xs, P, V, kk, i)
    sources = [i * G for i in range(2 * s)]
    cur = _cost(nbr, sources, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / iters) + 0.05
        if s == 1 or rng.random() < 0.7:
            kk = rng.randrange(d)
            i = rng.randrange(s)
            old = int(V[kk, i])
            new = rng.randrange(G)
            if new == old:
                continue
            V[kk, i] = new
            _set_dart(nbr, s, G, grp, xs, P, V, kk, i)
            c = _cost(nbr, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                V[kk, i] = old
                _set_dart(nbr, s, G, grp, xs, P, V, kk, i)
        else:
            kk = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            P[kk, a], P[kk, b] = P[kk, b], P[kk, a]
            _set_dart(nbr, s, G, grp, xs, P, V, kk, a)
            _set_dart(nbr, s, G, grp, xs, P, V, kk, b)
            c = _cost(nbr, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                P[kk, a], P[kk, b] = P[kk, b], P[kk, a]
                _set_dart(nbr, s, G, grp, xs, P, V, kk, a)
                _set_dart(nbr, s, G, grp, xs, P, V, kk, b)
    if cur == 0:
        return nbr, G
    return None


def _materialize(s, G, nbr):
    edges = set()
    for x in range(s * G):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * G, sorted(edges)


class _LiftState:
    """Bisection over group order m for one base size s and group order-k factor."""

    def __init__(self, s, k):
        self.s = s
        self.k = k
        self.m = 2
        self.lo = 0
        self.hi = None
        self.done = False

    def step(self, rng, d, D, cap, results, deadline):
        m = self.m
        G = m * self.k
        ok = None
        if 2 * self.s * G > cap:
            self.hi = m
        else:
            attempted = False
            for _ in range(RETRIES):
                now = time.monotonic()
                if now >= deadline:
                    break
                attempted = True
                grp = _pick_group(m, self.k, rng)
                ok = _anneal(self.s, grp, d, D, rng,
                             min(deadline, now + ATT_SLICE), ITERS)
                if ok is not None:
                    break
            if not attempted:
                return
            if ok is not None:
                nbr, GG = ok
                results.append(_materialize(self.s, GG, nbr))
        if ok is not None:
            self.lo = m
        else:
            self.hi = m
        if self.hi is None:
            self.m = 2 * self.lo
        elif self.hi - self.lo <= 1:
            self.done = True
        else:
            nm = (self.lo + self.hi) // 2
            if nm < 2:
                self.done = True
            else:
                self.m = nm


def _configs(D):
    cfg = [(s, 1) for s in range(1, 7)]          # cyclic lifts
    if D >= 5:
        cfg += [(s, k) for s in (1, 2) for k in (2, 3, 4)]   # non-abelian lifts
    return cfg


def _run_lifts(configs, rng, d, D, cap, results, deadline):
    states = [_LiftState(s, k) for s, k in configs]
    idx = 0
    while time.monotonic() < deadline:
        live = [st for st in states if not st.done]
        if not live:
            break
        st = live[idx % len(live)]
        idx += 1
        st.step(rng, d, D, cap, results, deadline)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    span = max(1.0, 0.8 * time_limit - 1.0)
    end = start + span
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    best = list(lib.haar_graph(d, range(d)))   # K_{d,d}: valid for D >= 2

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    bases = []
    if d >= 3:
        pg = _pg_base(d)
        if pg is not None:
            if D == 3 and lib.is_prime_power(d - 1):   # Moore-extremal
                consider(pg[0], pg[1])
                return best[0], best[1]
            bases.append(pg)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
                consider(gq[0], gq[1])
                return best[0], best[1]
            bases.append(gq)

    for g in bases:
        consider(g[0], g[1])

    # Growth of the algebraic base graphs.
    t_base = start + 0.15 * span
    for idx, g in enumerate(bases):
        now = time.monotonic()
        dl = now + max(0.0, t_base - now) / (len(bases) - idx)
        n2, e2 = _grow(g[0], g[1], d, D, rng, dl)
        consider(n2, e2)

    # Haar graphs with growing modulus (small slice).
    haar_end = time.monotonic() + 0.07 * span
    haar_m, haar_miss = d + 1, 0
    while time.monotonic() < haar_end and haar_miss < 4:
        S = _search_haar(d, D, haar_m, rng, haar_end, 120)
        if S is not None:
            n, e = lib.haar_graph(haar_m, S)
            consider(n, e)
            haar_miss = 0
        else:
            haar_miss += 1
        haar_m += 1

    # Voltage lifts (cyclic and non-abelian), round-robin bisection.
    cap = min(N_CAP, lib._moore_bound(d, D))
    results = []
    lift_end = start + 0.72 * span
    _run_lifts(_configs(D), rng, d, D, cap, results, lift_end)
    results.sort(key=lambda g: -g[0])
    for n, e in results:
        consider(n, e)

    # Fill spare degree and grow the largest lifts.
    post_end = start + 0.82 * span
    top = results[:POST_LIFTS]
    for idx, (n, e) in enumerate(top):
        now = time.monotonic()
        if now >= post_end:
            break
        dl = now + (post_end - now) / (len(top) - idx)
        n2, e2 = _grow(n, e, d, D, rng, dl)
        consider(n2, e2)

    # Iterated remove-and-regrow on the best valid graph.
    if D >= 3 and time.monotonic() < end and best[0] >= 4:
        n, e = _ils(best[0], best[1], d, D, rng, end)
        consider(n, e)

    return best[0], best[1]
