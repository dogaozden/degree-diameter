import math
import random
import time

import numpy as np

import lib

_BIG = 10 ** 9
_TABLES = {}
MAX_GROUPS = 4        # groups tried per (order, base size)
RESTARTS = 3          # annealing restarts per group
ANNEAL_ITERS = 2500   # annealing steps per restart


# ----------------------------------------------------------------------------
# Structured D = 3 baseline: incidence graph of PG(2, q).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products Z_m x|_r Z_k.
#
# Model: k base vertices A_0..A_{k-1} and k base vertices B_0..B_{k-1}, each
# lifted to a copy of the group G (|G| = M // k). Dart (i, j, s) joins
# A_{i,x} to B_{j,x*s} for all x in G. Each of the d layers is a perfect
# matching i -> perm[i] on the base vertices with one voltage per i, so every
# vertex has degree exactly d. Left translation is an automorphism, so the
# diameter is at most D iff every base vertex (A_i or B_j at identity) reaches
# everything within D steps. The cost counts unreached (source, vertex) pairs.
# ----------------------------------------------------------------------------

def _groups(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """(R, Ri): R[s, x] = x*s and Ri[s, x] = x*s^-1 for Z_m x|_r Z_k, element (a,b) coded a*k+b."""
    key = (m, k, r)
    hit = _TABLES.get(key)
    if hit is not None:
        return hit
    G = m * k
    P = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    X = np.arange(G, dtype=np.int64)
    a, b = X // k, X % k
    cs, ds = X // k, X % k
    R = ((a[None, :] + P[b][None, :] * cs[:, None]) % m) * k + (b[None, :] + ds[:, None]) % k
    nb = (-ds) % k
    invs = ((-P[nb] * cs) % m) * k + nb
    Ri = R[invs]
    val = (G, R, Ri)
    if len(_TABLES) >= 32:
        _TABLES.clear()
    _TABLES[key] = val
    return val


def _cost(k, G, D, darts, R, Ri):
    """Number of (source, vertex) pairs not within distance D, over the 2k base sources."""
    S = 2 * k
    VA = np.zeros((S, k, G), dtype=bool)
    VB = np.zeros((S, k, G), dtype=bool)
    for t in range(k):
        VA[t, t, 0] = True
        VB[k + t, t, 0] = True
    FA = VA.copy()
    FB = VB.copy()
    for _ in range(D):
        NA = np.zeros_like(VA)
        NB = np.zeros_like(VB)
        for i, j, s in darts:
            NB[:, j, :] |= FA[:, i, Ri[s]]
            NA[:, i, :] |= FB[:, j, R[s]]
        NB &= ~VB
        NA &= ~VA
        VB |= NB
        VA |= NA
        FA, FB = NA, NB
        if not (NA.any() or NB.any()):
            break
    return S * 2 * k * G - int(VA.sum()) - int(VB.sum())


def _anneal(d, D, k, G, R, Ri, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer matchings; returns darts with cost 0 or None."""
    volt = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    perm = [rng.sample(range(k), k) for _ in range(d)]

    def darts_now():
        return [(i, perm[L][i], volt[L][i]) for L in range(d) for i in range(k)]

    def cost_of(ds):
        if len(set(ds)) < len(ds):
            return _BIG
        return _cost(k, G, D, ds, R, Ri)

    cur_d = darts_now()
    cur = cost_of(cur_d)
    T0, T1 = 2.0, 0.05
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.6:
            i = rng.randrange(k)
            old = volt[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            volt[L][i] = new
            ds = darts_now()
            c2 = cost_of(ds)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur, cur_d = c2, ds
            else:
                volt[L][i] = old
        else:
            a, b = rng.sample(range(k), 2)
            perm[L][a], perm[L][b] = perm[L][b], perm[L][a]
            ds = darts_now()
            c2 = cost_of(ds)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur, cur_d = c2, ds
            else:
                perm[L][a], perm[L][b] = perm[L][b], perm[L][a]
    return cur_d if cur == 0 else None


def _edges(k, G, darts, R):
    E = []
    for i, j, s in darts:
        row = R[s].tolist()
        for x in range(G):
            E.append((i * G + x, (k + j) * G + row[x]))
    return 2 * k * G, E


def _try_order(d, D, M, deadline, rng, consider):
    """Try to build a valid lift on exactly M = k*G half-vertices; True if one was found."""
    for k in (2, 3, 1, 4):
        if M % k:
            continue
        G = M // k
        if G < 2:
            continue
        groups = _groups(G)
        rng.shuffle(groups)
        for m, kk, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                return False
            _, R, Ri = _tables(m, kk, r)
            for _ in range(RESTARTS):
                if time.monotonic() > deadline:
                    return False
                darts = _anneal(d, D, k, G, R, Ri, rng, deadline, ANNEAL_ITERS)
                if darts is not None:
                    n, edges = _edges(k, G, darts, R)
                    consider(n, edges)
                    return True
    return False


def _search(d, D, deadline, rng, get_n, consider):
    mmax = lib.moore_bound(d, D) // 2
    M = get_n() // 2 + 1
    while M <= mmax and time.monotonic() < deadline:
        if _try_order(d, D, M, deadline, rng, consider):
            M = max(M + 1, get_n() // 2 + 1)
        else:
            M += 1


# ----------------------------------------------------------------------------
# Diameter-preserving growth: add vertices whose neighbourhoods cover all
# vertices within D-1, then saturate spare degree with edges (both keep D).
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
        chosen.append(pool.pop(i))
        covered |= ball[chosen[-1]]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
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
            for attempt in range(60):
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
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


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)
    grow_slice = max(0.3, 0.05 * budget)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    def consider_grown(n, e):
        if not lib.is_valid(n, e, d, D):
            return
        consider(n, e)
        if best[0] < moore:
            gn, ge = _grow(n, e, d, D, min(deadline, time.monotonic() + grow_slice), rng)
            consider(gn, ge)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider_grown(pg[0], pg[1])

    if best[0] < moore:
        try:
            _search(d, D, deadline, rng, lambda: best[0], consider_grown)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
