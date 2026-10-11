import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact constructions (returned immediately when they are optimal).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (q <= 40)."""
    for q in range(min(d - 1, 40), 1, -1):
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to q <= 9 for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Number theory helpers.
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _primitive_root(p):
    phi = p - 1
    factors = []
    x = phi
    f = 2
    while f * f <= x:
        if x % f == 0:
            factors.append(f)
            while x % f == 0:
                x //= f
        f += 1
    if x > 1:
        factors.append(x)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in factors):
            return g
    return 1


# ----------------------------------------------------------------------------
# Group families. Each returns (G, Ts) with Ts[s, g] = g * s and identity at 0.
# ----------------------------------------------------------------------------

def _affine_table(p, t):
    """Affine group {x -> a x + b over Z_p : a in H}, |H| = t, t | p-1. Order p*t."""
    g0 = _primitive_root(p)
    h = pow(g0, (p - 1) // t, p)
    H = [pow(h, j, p) for j in range(t)]
    pos = np.full(p, -1, dtype=np.int64)
    for i, v in enumerate(H):
        pos[v] = i
    G = p * t
    idx = np.arange(G, dtype=np.int64)
    Hv = np.array(H, dtype=np.int64)
    A = Hv[idx // p]
    B = idx % p
    Ts = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        a2 = H[s // p]
        b2 = s % p
        na = (A * a2) % p
        nb = (A * b2 + B) % p
        Ts[s] = pos[na] * p + nb
    return G, Ts


def _semidirect_table(m, k2, r):
    """Z_m x|_r Z_k2 with (a,b)(c,e) = (a + r^b c, b + e); element a*k2+b."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    return G, Ts


def _invert(G, Ts):
    """Invs[s, h] = the g with g*s = h."""
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(np.arange(G, dtype=np.int64)[None, :], (G, G))
    return Invs


def _sample_affine(target, rng):
    """Return (p, t) for the affine group of order p*t >= target, or None."""
    ts = list(range(1, 13))
    rng.shuffle(ts)
    for t in ts[:6]:
        p0 = max(3, -(-target // t))
        start = p0 + rng.randrange(0, 30)
        for p in range(start, start + 300):
            if p * t > 1500:
                break
            if (p - 1) % t == 0 and _is_prime(p):
                return p, t
    return None


def _sample_semi(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        if m * k2 > 1500:
            continue
        return m, k2, r
    return None


def _sample_group(target, rng):
    """Return a group tables triple (G, Ts, Invs) of order >= target, or None."""
    if rng.random() < 0.5:
        aff = _sample_affine(target, rng)
        if aff is not None:
            p, t = aff
            G, Ts = _affine_table(p, t)
            return G, Ts, _invert(G, Ts)
    sm = _sample_semi(target, rng)
    if sm is None:
        return None
    m, k2, r = sm
    G, Ts = _semidirect_table(m, k2, r)
    return G, Ts, _invert(G, Ts)


# ----------------------------------------------------------------------------
# Bi-Cayley lifts with k base vertices per side, with PARTIAL layers.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h. Index N = 2kG is a
# dummy vertex with no neighbours, used for "no edge" entries.
# Layer l maps A-base i to B-base tg[l][i] (or -1 for none), through voltage
# S[l][i]: A_{i,g} ~ B_{j, g*s}. Each layer is an injective partial map, so every
# vertex gets at most one neighbour per layer and degree stays <= d.
#
# New routine: partial last layer + greedy deficit filling. The search anneals
# over the layers with the last one allowed to leave base vertices unmatched.
# After the search finds diameter <= D, every unmatched block is joined to
# other deficient blocks greedily. Adding edges never increases distances, so
# the result stays valid. Full-layer mode (partial=False) is the parent's search.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _write_layer(nbr, k, G, Ts, Invs, N, l, tg, S):
    """Rewrite layer l's neighbour arrays from the target map tg and voltages S."""
    nbr[l, :] = N
    for i in range(k):
        j = tg[i]
        if j < 0:
            continue
        s = S[i]
        nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
        nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _cost(k, G, D, nbr, N):
    """Unreached (representative, vertex) pairs over all 2k representatives."""
    d = nbr.shape[0]
    reach = np.zeros(N + 1, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return 2 * k * N - int(_POP[reach[:N]].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, partial):
    """Annealing over voltages, target swaps and (optionally) unmatched slots.

    Returns (N, set_of_A_to_B_edges) on success, or None.
    """
    N = 2 * k * G
    tg = [rng.sample(range(k), k) for _ in range(d)]
    if partial:
        u = rng.randint(1, k)
        for i in rng.sample(range(k), u):
            tg[-1][i] = -1
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N + 1), dtype=np.int64)
    for l in range(d):
        _write_layer(nbr, k, G, Ts, Invs, N, l, tg[l], S[l])

    def dupcount():
        keys = [(i, tg[l][i], S[l][i]) for l in range(d) for i in range(k) if tg[l][i] >= 0]
        return len(keys) - len(set(keys))

    cost = _cost(k, G, D, nbr, N) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    choices_lo = -1 if partial else 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)
        old_tg = tg[l][:]
        old_S = S[l][:]
        r = rng.random()
        if k > 1 and r < 0.3:
            i1, i2 = rng.sample(range(k), 2)
            tg[l][i1], tg[l][i2] = tg[l][i2], tg[l][i1]
        elif r < 0.45:
            i = rng.randrange(k)
            v = rng.choice(range(choices_lo, k))
            if v == tg[l][i]:
                continue
            if v >= 0 and v in tg[l]:
                idx = tg[l].index(v)
                tg[l][i], tg[l][idx] = tg[l][idx], tg[l][i]
            else:
                tg[l][i] = v
        else:
            i = rng.randrange(k)
            if tg[l][i] < 0:
                continue
            new = rng.randrange(G)
            if new == S[l][i]:
                continue
            S[l][i] = new

        _write_layer(nbr, k, G, Ts, Invs, N, l, tg[l], S[l])
        c2 = _cost(k, G, D, nbr, N) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            tg[l] = old_tg
            S[l] = old_S
            _write_layer(nbr, k, G, Ts, Invs, N, l, tg[l], S[l])

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for l in range(d):
            v = int(nbr[l, u])
            if v < N:
                edges.add((u, v))
    return N, edges


def _fill(N, k, G, d, edges, rng):
    """Greedily add A-B edges between vertices of degree < d. Never increases distances."""
    deg = [0] * N
    adj = [set() for _ in range(N)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    A = [u for u in range(k * G) if deg[u] < d]
    B = [v for v in range(k * G, N) if deg[v] < d]
    rng.shuffle(A)
    rng.shuffle(B)
    for a in A:
        for b in B:
            if deg[a] >= d:
                break
            if deg[b] < d and b not in adj[a]:
                edges.add((a, b))
                deg[a] += 1
                deg[b] += 1
                adj[a].add(b)
                adj[b].add(a)
    return edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions: return immediately when they are record-optimal.
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

    # Main search: bandit over arms (base size k, full or partial last layer).
    arms = [(k, p) for k in _KS for p in (False, True)]
    trials = {a: 0 for a in arms}
    wins = {a: 0 for a in arms}

    def pick():
        if rng.random() < 0.2:
            return rng.choice(arms)
        return max(arms, key=lambda a: (wins[a] + 1) / (trials[a] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        arm = pick()
        k, partial = arm
        base = best_n // (2 * k)
        if rng.random() < 0.25:
            target = base + base // 10 + 1 + rng.randrange(0, max(2, base // 10 + 1))
        else:
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        G, Ts, Invs = g
        if 2 * k * G <= best_n:
            continue
        trials[arm] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, partial)
        if res is not None:
            N, edges = res
            edges = _fill(N, k, G, d, edges, rng)
            wins[arm] += 1
            consider(N, sorted(edges))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
