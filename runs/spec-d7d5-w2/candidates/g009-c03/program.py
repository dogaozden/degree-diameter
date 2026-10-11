import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / small constructions (fallbacks and calibration cases).
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Family A (baseline): bi-Cayley lifts over Z_m x| Z_k2 with k blocks per side.
# Kept as a safe baseline; it secures a large valid graph early.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
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


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Family B (new, bold): Haar graphs over arbitrary small groups.
#
# Vertices A_g = g and B_h = G + h for g, h in the group. Connection set S of
# size d: A_g ~ B_{g s} for s in S. Left multiplication is an automorphism, so
# only two BFS runs are needed: from A_1 (covers A-A within D, A-B within D) and
# from B_1 (covers B-B within D). Groups are semidirect products Z_m x| Z_k2,
# including direct products (r = 1), so non-cyclic groups are used.
# A simulated annealing search over S minimises unreached pairs.
# ----------------------------------------------------------------------------

def _group_options(G):
    """All (m, k2, r) with m * k2 == G, m >= 2, r^k2 = 1 mod m, gcd(r, m) = 1."""
    opts = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
    return opts


def _group_table(m, k2, r):
    """Multiplication table M (G x G) and inverse array for Z_m x| Z_k2; identity is index 0."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    rp = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + rp[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    return M, inv


def _haar_defects(NB, NA, G, D):
    """Count unreached pairs from A_1 (all A and B) and from B_1 (all B) within distance D."""
    total = 0
    for from_a in (True, False):
        visA = np.zeros(G, dtype=bool)
        visB = np.zeros(G, dtype=bool)
        front = np.array([0], dtype=np.int64)
        if from_a:
            visA[0] = True
        else:
            visB[0] = True
        on_a = from_a
        for _ in range(D):
            if front.size == 0:
                break
            mask = np.zeros(G, dtype=bool)
            if on_a:
                mask[NB[front].ravel()] = True
                new = mask & ~visB
                visB |= new
            else:
                mask[NA[front].ravel()] = True
                new = mask & ~visA
                visA |= new
            front = np.flatnonzero(new)
            on_a = not on_a
        total += G - int(visB.sum())
        if from_a:
            total += G - int(visA.sum())
    return total


def _anneal(M, inv, G, d, D, rng, deadline, iters):
    """Anneal a d-element connection set S in the group; return S with zero defects, or None."""
    S = rng.sample(range(G), d)

    def ev(S_):
        Sa = np.array(S_, dtype=np.int64)
        return _haar_defects(M[:, Sa], M[:, inv[Sa]], G, D)

    cost = ev(S)
    inS = set(S)
    for t in range(iters):
        if cost == 0:
            break
        if (t & 31) == 0 and time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - t / iters) + 0.1
        j = rng.randrange(d)
        new = rng.randrange(G)
        if new in inS:
            continue
        old = S[j]
        S[j] = new
        c2 = ev(S)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            inS.discard(old)
            inS.add(new)
            cost = c2
        else:
            S[j] = old
    return list(S) if cost == 0 else None


def _haar_stage(best, d, D, rng, deadline):
    """Exponential ladder over the group order G: try n = 2G > best order, back off on failure."""
    base = best[0] // 2
    step = 8
    while time.monotonic() < deadline:
        G = base + step
        opts = _group_options(G)
        found = None
        if opts:
            attempt_end = min(deadline, time.monotonic() + 3.0)
            while time.monotonic() < attempt_end and found is None:
                m, k2, r = rng.choice(opts)
                M, inv = _group_table(m, k2, r)
                S = _anneal(M, inv, G, d, D, rng, attempt_end, 3000)
                if S is not None:
                    found = (M, S)
        if found is not None:
            M, S = found
            n2 = 2 * G
            e2 = [(g, G + int(M[g, s])) for g in range(G) for s in S]
            if lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
                base = G
                step = min(2 * step, 256)
                continue
        step = max(1, step // 2)
    return best


# ----------------------------------------------------------------------------
# Greedy pair insertion (validated by lib.is_valid at every step).
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    adj = lib.adjacency(n, edges)
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


def _extend(n, edges, d, D, rng, deadline):
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    while time.monotonic() < deadline:
        order = list(range(len(edges)))
        rng.shuffle(order)
        chosen = []
        used_a, used_b = set(), set()
        for t in order:
            if len(chosen) == d - 1:
                break
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            if a in used_a or b in used_b:
                continue
            chosen.append(t)
            used_a.add(a)
            used_b.add(b)
        if len(chosen) < d - 1:
            break
        x, y = n, n + 1
        cs = set(chosen)
        cand = [e for t, e in enumerate(edges) if t not in cs]
        for t in chosen:
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            cand.append((x, b))
            cand.append((y, a))
        cand.append((x, y))
        if lib.is_valid(n + 2, cand, d, D):
            edges = cand
            n += 2
            color.extend([0, 1])
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < start + 0.3 * budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    search_end = start + 0.85 * budget
    p1_end = start + 0.3 * budget

    # Phase 1: bi-Cayley baseline (safe, gives a strong graph early).
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < p1_end:
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best[0]:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, p1_end, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase 2 (bold): Haar graphs over non-cyclic groups, aiming above the baseline.
    best = _haar_stage(best, d, D, rng, search_end)

    # Phase 3: greedy pair insertion on the best graph, validated each step.
    try:
        n2, e2 = _extend(best[0], best[1], d, D, rng, deadline)
        consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
