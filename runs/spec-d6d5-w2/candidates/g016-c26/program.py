import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over groups G (order G): vertices A_x and B_w (x, w in G),
# edges A_x ~ B_{x*s} for s in S, |S| = dp. Left multiplication is an
# automorphism, so validity only needs BFS from A_1 and B_1.
#
# NEW in this version: degree-(d-1) bi-Cayley bases are annealed, then boosted
# to degree d by _boost. _boost greedily adds cross-side edges between
# deficient vertices, choosing for each vertex the partner that reaches the
# most currently unreached vertices. Adding edges never increases distances,
# so the boosted graph is valid whenever it reaches diameter D, and every
# candidate still goes through lib.is_valid before it is kept.
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


def _group_specs(lo, hi):
    """Group specs with order in [lo, hi]: AGL(1,p) and semidirect Z_m x| Z_k."""
    specs = []
    for p in range(3, hi + 2):
        o = p * (p - 1)
        if lo <= o <= hi and _is_prime(p):
            specs.append((o, ("aff", p)))
    for m in range(2, hi + 1):
        for k in range(1, hi // m + 1):
            o = m * k
            if o < lo or o > hi:
                continue
            if k == 1:
                specs.append((o, ("sd", m, 1, 1)))
                continue
            found = 0
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    specs.append((o, ("sd", m, k, r)))
                    found += 1
                    if found >= 2:
                        break
    return specs


def _group_table(spec):
    """Return (order, mul_table) as an int64 numpy array; identity is code 0."""
    if spec[0] == "aff":
        p = spec[1]
        G = p * (p - 1)
        X = np.arange(G, dtype=np.int64)
        u = X // p + 1
        b = X % p
        U = u[:, None]
        B = b[:, None]
        V = u[None, :]
        C = b[None, :]
        T = ((U * V) % p - 1) * p + (U * C + B) % p
        return G, T
    _, m, k, r = spec
    G = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    X = np.arange(G, dtype=np.int64)
    a = X // k
    b = X % k
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    Dd = b[None, :]
    T = ((A + pw[B] * C) % m) * k + (B + Dd) % k
    return G, T


def _bc_adj(M, inv, S, G):
    Sa = np.asarray(S, dtype=np.int64)
    return np.vstack([G + M[:, Sa], M[:, inv[Sa]]])


def _bc_cost(adj, G, D):
    """Unreached (vertex, source) count from A_1 and B_1 within D steps. Zero means valid."""
    N = adj.shape[0]
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            frontier = nb
        total += N - int(np.count_nonzero(seen))
    return total


def _anneal_bc(M, inv, G, dp, D, deadline, rng, iters):
    """Anneal a connection set S (|S| = dp). Returns (best_S, best_cost)."""
    S = rng.sample(range(G), dp)
    c = _bc_cost(_bc_adj(M, inv, S, G), G, D)
    bestS, bestc = list(S), c
    T = 1.5
    for _ in range(iters):
        if bestc == 0 or time.monotonic() >= deadline:
            break
        T = max(0.1, T * 0.998)
        i = rng.randrange(dp)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = list(S)
        S2[i] = x
        c2 = _bc_cost(_bc_adj(M, inv, S2, G), G, D)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            S, c = S2, c2
            if c < bestc:
                bestS, bestc = list(S), c
    return bestS, bestc


def _bc_edges(M, S, G):
    E = []
    for x in range(G):
        row = M[x]
        for s in S:
            E.append((x, G + int(row[s])))
    return E


# ----------------------------------------------------------------------------
# Ball bitmasks and the boost routine.
# ----------------------------------------------------------------------------

def _balls(n, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _boost(n, edges, color, d, D, deadline, rng):
    """Greedily add cross-colour edges between deficient vertices to reduce far pairs.

    Each vertex u picks, from random deficient partners, the one whose ball covers
    the most vertices u cannot yet reach. Returns the enlarged edge list.
    """
    out = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in out:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((u, v) if u < v else (v, u))
    full = (1 << n) - 1
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D)
        if all(b == full for b in ball):
            break
        deficient = [[v for v in range(n) if color[v] == c and len(adj[v]) < d] for c in (0, 1)]
        order = deficient[0] + deficient[1]
        rng.shuffle(order)
        used = set()
        added = 0
        for u in order:
            if time.monotonic() >= deadline:
                break
            if len(adj[u]) >= d or u in used:
                continue
            pool = deficient[1 - color[u]]
            if not pool:
                continue
            unreached = full & ~ball[u]
            if unreached == 0:
                continue
            best_v, best_g = -1, -1
            for _ in range(40):
                v = pool[rng.randrange(len(pool))]
                if v in used or len(adj[v]) >= d or not (unreached >> v) & 1:
                    continue
                g = (ball[v] & unreached).bit_count()
                if g > best_g:
                    best_g, best_v = g, v
            if best_v < 0:
                continue
            v = best_v
            key = (u, v) if u < v else (v, u)
            if key in existing:
                continue
            existing.add(key)
            adj[u].append(v)
            adj[v].append(u)
            out.append((u, v))
            used.add(u)
            used.add(v)
            added += 1
        if added == 0:
            break
    return out


# ----------------------------------------------------------------------------
# Small-D families and fallbacks.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 2:
        return best_n, best_e

    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                consider(*lib.araujo_lopez_graph(q))
            except Exception:
                pass
        if not lib.is_valid(best_n, best_e, d, D):
            best_n, best_e = lib.haar_graph(d, range(d))
        return best_n, best_e

    # D >= 4: bi-Cayley search over groups of order near the target window.
    # Interleave degree-d anneals (cost 0 gives a direct graph) with
    # degree-(d-1) anneals followed by the boost to degree d.
    moore = lib.moore_bound(d, D)
    lo = max(2 * d, int(0.4 * moore / 2))
    hi = min(lo + max(24, lo // 6), 420)
    specs = _group_specs(lo, hi) if lo <= hi else []
    cache = {}
    slice_len = 1.5

    while time.monotonic() < deadline and specs:
        cutoff = best_n // 2
        pool = [s for s in specs if s[0] > cutoff]
        if not pool:
            break
        o, spec = pool[rng.randrange(len(pool))]
        if spec not in cache:
            if len(cache) > 40:
                cache.clear()
            G, M = _group_table(spec)
            inv = np.argmax(M == 0, axis=1)
            cache[spec] = (G, M, inv)
        G, M, inv = cache[spec]

        dp = d if rng.random() < 0.6 else d - 1
        if dp < 1 or dp > G:
            continue
        slice_end = min(deadline, time.monotonic() + slice_len)
        S, c = _anneal_bc(M, inv, G, dp, D, slice_end, rng, 4000)

        if dp == d:
            if c == 0:
                consider(2 * G, _bc_edges(M, S, G))
        else:
            n = 2 * G
            E = _bc_edges(M, S, G)
            color = [0] * G + [1] * G
            boost_end = min(deadline, time.monotonic() + 2.0)
            E2 = _boost(n, E, color, d, D, boost_end, rng)
            consider(n, E2)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
