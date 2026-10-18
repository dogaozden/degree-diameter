import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (exact constructions, always valid).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_MAX_K = 8          # reach bitmasks use 2k <= 16 bits
_GROUP_CAP = 1700   # largest group order we tabulate


def _is_prime(n):
    return n >= 2 and all(n % q for q in range(2, int(n ** 0.5) + 1))


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
# Slack extension: add vertices using spare degree; only valid graphs kept.
# ----------------------------------------------------------------------------

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
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
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
                cand = edges + [(v, n) for v in pick]
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
# NEW FAMILY: bi-Cayley lifts over NON-abelian groups with closed-form
# multiplication: Heisenberg groups H(p) (unitriangular 3x3 over Z_p),
# SL(2,p), and affine groups AGL(1,p). The parent searched metacyclic
# semidirect products only.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} via voltage s: A_{i,g} ~ B_{p,g*s}.
# Each layer is a permutation of blocks, so every vertex has degree d.
# Left multiplication is an automorphism, so diameter reduces to checking
# distances from the 2k block representatives (identity elements).
# ----------------------------------------------------------------------------

def _build_group(fam, p):
    """Return (G, Ts, Invs): Ts[s, g] = index of g*s, Invs[s, h] = index of g with g*s = h."""
    if fam == "heis":
        R = p ** 3
        vals = np.arange(R, dtype=np.int64)
        E = np.stack([vals // (p * p), (vals // p) % p, vals % p], axis=1)

        def prod(X, Y):
            a1, b1, c1 = X[..., 0], X[..., 1], X[..., 2]
            a2, b2, c2 = Y[..., 0], Y[..., 1], Y[..., 2]
            return np.stack([(a1 + a2) % p, (b1 + b2) % p, (c1 + c2 + a1 * b2) % p], axis=-1)

        def enc(C):
            return (C[..., 0] * p + C[..., 1]) * p + C[..., 2]

    elif fam == "sl2":
        mats = [m for m in itertools.product(range(p), repeat=4)
                if (m[0] * m[3] - m[1] * m[2]) % p == 1]
        E = np.array(mats, dtype=np.int64)
        R = p ** 4

        def prod(X, Y):
            a1, b1, c1, d1 = (X[..., i] for i in range(4))
            a2, b2, c2, d2 = (Y[..., i] for i in range(4))
            return np.stack([(a1 * a2 + b1 * c2) % p, (a1 * b2 + b1 * d2) % p,
                             (c1 * a2 + d1 * c2) % p, (c1 * b2 + d1 * d2) % p], axis=-1)

        def enc(C):
            return ((C[..., 0] * p + C[..., 1]) * p + C[..., 2]) * p + C[..., 3]

    elif fam == "agl":
        E = np.array([(a, b) for a in range(1, p) for b in range(p)], dtype=np.int64)
        R = p * p

        def prod(X, Y):
            a1, b1 = X[..., 0], X[..., 1]
            a2, b2 = Y[..., 0], Y[..., 1]
            return np.stack([(a1 * a2) % p, (a1 * b2 + b1) % p], axis=-1)

        def enc(C):
            return C[..., 0] * p + C[..., 1]
    else:
        raise ValueError(fam)

    G = len(E)
    lookup = np.full(R, -1, dtype=np.int64)
    lookup[enc(E)] = np.arange(G)
    M = lookup[enc(prod(E[:, None, :], E[None, :, :]))]
    if (M < 0).any():
        raise ValueError("group not closed")
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.arange(G)[None, :]
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Layer l: A-block i is matched to B-block j with voltage s (both sides written)."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bit b of reach[v] is set when block-representative b is within distance D of v."""
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


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing over layers and voltages. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def cost_of(reach):
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return _unreached(k, N, reach) + _PENALTY * (len(keys) - len(set(keys)))

    def rewrite(l, i):
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    reach = _reach(k, G, D, nbr, d)
    cost = cost_of(reach)
    c0 = float(max(cost, 1))
    best_cost, last = cost, 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last > patience:
            break
        temp = max(0.5, 0.02 * c0 * (1.0 - t / iters))

        if k >= 2 and rng.random() < 0.25:
            # Swap the B-targets of two A-blocks within one layer.
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            rewrite(l, i1)
            rewrite(l, i2)
            r2 = _reach(k, G, D, nbr, d)
            c2 = cost_of(r2)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                rewrite(l, i1)
                rewrite(l, i2)
            continue

        # Voltage move, defect-targeted half of the time.
        bad = np.flatnonzero(reach != full) if rng.random() < 0.5 else np.empty(0, dtype=np.int64)
        if bad.size:
            u = int(bad[rng.randrange(bad.size)])
            blk = u // G
            l = rng.randrange(d)
            i = blk if blk < k else layers[l].index(blk - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        rewrite(l, i)
        r2 = _reach(k, G, D, nbr, d)
        c2 = cost_of(r2)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last = cost, t
        else:
            S[l][i] = old
            rewrite(l, i)

    if cost != 0:
        return None
    edges = []
    for u in range(k * G):
        for v in sorted(set(nbr[:, u].tolist())):
            edges.append((u, v))
    return N, edges


def _specs():
    """Candidate (family, p, order) groups with order at most _GROUP_CAP."""
    out = []
    for p in (5, 7, 11):
        out.append(("heis", p, p ** 3))
        out.append(("sl2", p, p * (p * p - 1)))
    for p in range(7, 60):
        if _is_prime(p) and p * (p - 1) <= _GROUP_CAP:
            out.append(("agl", p, p * (p - 1)))
    return [s for s in out if s[2] <= _GROUP_CAP]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget_end = t0 + max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    final_end = t0 + max(1.0, time_limit - 3.0)
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

    try:
        if d == 2 and D >= 2:
            consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])

        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best

        if D == 4 and time.monotonic() < budget_end:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
                if d - 1 <= 9 and lib.is_prime_power(d - 1):
                    return best

        if D == 2:
            return best

        # Main search over non-abelian bi-Cayley lifts.
        moore = lib.moore_bound(d, D)
        specs = _specs()
        tries = {}
        cache = {}
        while time.monotonic() < budget_end:
            cands = []
            for fam, p, G in specs:
                for k in range(1, _MAX_K + 1):
                    n = 2 * k * G
                    if best_n < n <= moore:
                        cands.append((fam, p, G, k, n))
            if not cands:
                break

            def score(c, cur=best_n):
                fam, p, G, k, n = c
                return (tries.get((fam, p, k), 0)
                        + 4.0 * (n - cur) / max(cur, 1)
                        + 0.5 * rng.random())

            fam, p, G, k, n = min(cands, key=score)
            tries[(fam, p, k)] = tries.get((fam, p, k), 0) + 1
            try:
                if (fam, p) not in cache:
                    if len(cache) >= 3:
                        cache.clear()
                    cache[(fam, p)] = _build_group(fam, p)
                Gg, Ts, Invs = cache[(fam, p)]
                res = _search(d, D, k, Gg, Ts, Invs, rng, budget_end, 4000, 900)
                if res is not None:
                    consider(res[0], res[1])
            except Exception:
                continue

        if time.monotonic() < final_end:
            n2, e2 = _slack_extend(best_n, best[1], d, D, rng, final_end)
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
