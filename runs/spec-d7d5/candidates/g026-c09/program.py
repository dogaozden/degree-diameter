import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent for non-target cases).
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension (parent's greedy step; still used as a final polish).
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Semidirect group tables.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


# ----------------------------------------------------------------------------
# NEW: orbit augmentation of bi-Cayley lifts.
#
# A lift with dp = d - t layers leaves every vertex t spare degree. Instead of
# only greedily adding single vertices, we add two whole G-orbits:
#   * a new A-block whose vertices use d "uses" (j, s) into existing B-blocks,
#   * a new B-block whose vertices use d "uses" (i, s) into existing A-blocks.
# A use (j, s) joins A_{new,g} to B_{j, g*s}; it is equivariant under left
# multiplication, so the whole graph keeps the group action and the search
# only needs one representative per block. Each old block may take at most t
# extra uses, so no degree exceeds d. Validity is always confirmed by lib.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _valid_uses(uses, k, t, d):
    """Uses are distinct (block, voltage) pairs, exactly d of them, at most t per old block."""
    if len(uses) != d:
        return False
    cnt = [0] * k
    seen = set()
    for j, s in uses:
        if (j, s) in seen:
            return False
        seen.add((j, s))
        cnt[j] += 1
        if cnt[j] > t:
            return False
    return True


def _random_uses(k, t, d, G, rng):
    """Random valid list of d uses, or None."""
    for _ in range(50):
        uses = []
        cnt = [0] * k
        seen = set()
        tries = 0
        while len(uses) < d and tries < 400:
            tries += 1
            j = rng.randrange(k)
            s = rng.randrange(G)
            if cnt[j] >= t or (j, s) in seen:
                continue
            seen.add((j, s))
            cnt[j] += 1
            uses.append((j, s))
        if len(uses) == d:
            return uses
    return None


def _make_nbr(d, k, K, G, Ts, Invs, layers, S, uA, uB):
    """Neighbour matrix of shape (d, N+1); column N is a sentinel pointing to itself.

    Vertex blocks: A-block i at i*G, B-block j at (K+j)*G. Lift rows come first.
    With augmentation, block K-1 is the new A block (uses uA) and the new B block (uses uB).
    """
    N = 2 * K * G
    nbr = np.full((d, N + 1), N, dtype=np.int64)
    dp = len(layers)
    for l in range(dp):
        for i in range(k):
            j = layers[l][i]
            s = S[l][i]
            nbr[l, i * G:(i + 1) * G] = (K + j) * G + Ts[s]
            nbr[l, (K + j) * G:(K + j + 1) * G] = i * G + Invs[s]
    if uA is not None:
        a_new = K - 1
        b_new = K - 1
        free_a = [dp] * k
        free_b = [dp] * k
        for p, (j, s) in enumerate(uA):
            nbr[p, a_new * G:(a_new + 1) * G] = (K + j) * G + Ts[s]
            r = free_b[j]
            free_b[j] += 1
            nbr[r, (K + j) * G:(K + j + 1) * G] = a_new * G + Invs[s]
        for p, (i, s) in enumerate(uB):
            nbr[p, (K + b_new) * G:(K + b_new + 1) * G] = i * G + Invs[s]
            r = free_a[i]
            free_a[i] += 1
            nbr[r, i * G:(i + 1) * G] = (K + b_new) * G + Ts[s]
    return nbr


def _reach(N, K, G, D, nbr):
    """Bitmask per vertex: bit b set when block b's representative is within distance D."""
    reach = np.zeros(N + 1, dtype=np.int64)
    for b in range(2 * K):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(nbr.shape[0]):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(N, K, reach):
    """Number of unreached (vertex, block) pairs."""
    return 2 * K * N - int(_POP[reach[:N]].sum())


def _search(d, D, k, t, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing over lift voltages and augmentation uses.

    t = 0 is a plain lift with d layers. t > 0 uses dp = d - t layers plus two new blocks.
    Returns (n, edges) or None.
    """
    augment = t > 0
    dp = d - t
    K = k + 1 if augment else k
    N = 2 * K * G
    layers = [rng.sample(range(k), k) for _ in range(dp)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(dp)]
    uA = None
    uB = None
    if augment:
        uA = _random_uses(k, t, d, G, rng)
        uB = _random_uses(k, t, d, G, rng)
        if uA is None or uB is None:
            return None

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(dp) for i in range(k)]
        return len(keys) - len(set(keys))

    def score():
        nbr = _make_nbr(d, k, K, G, Ts, Invs, layers, S, uA, uB)
        reach = _reach(N, K, G, D, nbr)
        return _unreached(N, K, reach) + _PENALTY * dupcount()

    cost = score()
    c0 = float(max(cost, 1))
    best_cost = cost
    last = 0
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if it - last > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - it / iters))
        x = rng.random()

        if augment and x < 0.35:
            # Augmentation move: change one use of the new A or new B block.
            lst = uB if rng.random() < 0.5 else uA
            p = rng.randrange(d)
            old = lst[p]
            new = (rng.randrange(k), rng.randrange(G))
            if new == old:
                continue
            cand = lst[:p] + [new] + lst[p + 1:]
            if not _valid_uses(cand, k, t, d):
                continue
            lst[p] = new
            c2 = score()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
                if cost < best_cost:
                    best_cost, last = cost, it
            else:
                lst[p] = old
            continue

        if k >= 2 and x < 0.5:
            # Layer swap: exchange the B-targets of two A-blocks in one layer.
            l = rng.randrange(dp)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            c2 = score()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
                if cost < best_cost:
                    best_cost, last = cost, it
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            continue

        # Voltage move on a lift dart.
        l = rng.randrange(dp)
        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        c2 = score()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost < best_cost:
                best_cost, last = cost, it
        else:
            S[l][i] = old

    if cost != 0:
        return None
    nbr = _make_nbr(d, k, K, G, Ts, Invs, layers, S, uA, uB)
    edges = set()
    for u in range(N):
        for l in range(d):
            v = int(nbr[l, u])
            if v < N:
                edges.add((u, v) if u < v else (v, u))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, time_limit - 6.0)
    final_deadline = start + max(1.0, time_limit - 3.0)
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

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Candidate (k, t) pairs: t = 0 is a plain lift; t > 0 needs k*t >= d and d - t >= 1.
    cands = []
    for k in range(1, 5):
        for t in range(0, d):
            if t == 0 or k * t >= d:
                cands.append((k, t))
    if not cands:
        cands = [(1, 0)]
    trials = {c: 0 for c in cands}
    wins = {c: 0 for c in cands}

    def pick():
        if rng.random() < 0.2:
            return rng.choice(cands)
        return max(cands, key=lambda c: (wins[c] + 1) / (trials[c] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k, t = pick()
        K = k + 1 if t > 0 else k
        base = best_n // (2 * K)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if m * k2 > 2000 or 2 * K * m * k2 <= best_n:
            continue
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        trials[(k, t)] += 1
        try:
            res = _search(d, D, k, t, G, Ts, Invs, rng, deadline, 4000, 1200)
        except Exception:
            res = None
        if res is not None:
            wins[(k, t)] += 1
            consider(res[0], res[1])

    # Greedy polish with any spare degree.
    if time.monotonic() < final_deadline:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
