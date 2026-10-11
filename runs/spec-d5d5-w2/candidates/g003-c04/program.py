import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products Z_m x|_r Z_k, searched by
# simulated annealing. The cost counts (source layer, vertex) pairs at distance
# more than D. Each layer is vertex-transitive under left multiplication by the
# group, so one source per layer suffices. The BFS uses fancy indexing only,
# with no BLAS, so it stays single-threaded.
# ----------------------------------------------------------------------------

ITERS = 6000        # annealing steps per (group, k) attempt
MAX_V = 1500        # cap on vertex count for the dense search (keeps each step fast)
GROUPS_PER_G = 3    # groups tried for each order before resampling k and G


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Multiplication table T[x, s] = x*s for Z_m x|_r Z_k, and inverses invs[s]."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, e, m) for e in range(k)], dtype=np.int64)
    prod = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    T = prod * k + (b[:, None] + b[None, :]) % k
    invs = np.argmax(T == 0, axis=1)  # T[s, y] = 0 exactly when y = s^-1
    return T, invs


def _cost(k, G, D, d, darts, T, invs):
    """Number of (layer source, vertex) pairs not reached within distance D. Zero means valid."""
    V = 2 * k * G
    L = 2 * k
    ar = np.arange(G)
    nbr = np.zeros((V, d), dtype=np.int64)
    cnt = np.zeros(V, dtype=np.int64)
    for i, j, s in darts:
        ra = i * G + ar
        ca = (k + j) * G + T[:, s]
        nbr[ra, cnt[ra]] = ca
        cnt[ra] += 1
        rb = (k + j) * G + ar
        cb = i * G + T[ar, invs[s]]
        nbr[rb, cnt[rb]] = cb
        cnt[rb] += 1
    frontier = np.zeros((V, L), dtype=bool)
    frontier[np.arange(L) * G, np.arange(L)] = True
    seen = frontier.copy()
    for _ in range(D):
        nxt = frontier[nbr].any(axis=1)
        nxt &= ~seen
        if not nxt.any():
            break
        seen |= nxt
        frontier = nxt
    return L * V - int(seen.sum())


def _valid_keys(darts):
    """True if all darts (i, j, s) are distinct, so no edge is produced twice."""
    return len({(i, j, s) for i, j, s in darts}) == len(darts)


def _anneal(d, D, k, G, T, invs, rng, deadline, iters):
    """Anneal voltages and per-layer target assignments. Returns darts with cost 0, else None.

    Dart index L*k + i is the layer-L dart out of A_i. Each layer is a permutation i -> j,
    so every vertex has degree exactly d.
    """
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    for _ in range(200):
        if _valid_keys(darts):
            break
        for dt in darts:
            dt[2] = rng.randrange(G)
    if not _valid_keys(darts):
        return None

    cost = _cost(k, G, D, d, darts, T, invs)
    best_cost = cost
    best = [list(x) for x in darts]
    T0 = 1.0 + 0.1 * cost

    for step in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, T0 * (1.0 - step / iters))
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            s_old = darts[idx][2]
            s_new = rng.randrange(G)
            if s_new == s_old:
                continue
            darts[idx][2] = s_new
            if not _valid_keys(darts):
                darts[idx][2] = s_old
                continue
            c2 = _cost(k, G, D, d, darts, T, invs)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[idx][2] = s_old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            ok = _valid_keys(darts)
            if ok:
                c2 = _cost(k, G, D, d, darts, T, invs)
                ok = c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp)
                if ok:
                    cost = c2
            if not ok:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
        if cost < best_cost:
            best_cost = cost
            best = [list(x) for x in darts]

    return best if best_cost == 0 else None


def _edges(k, G, T, darts):
    """Edge list and order of the lift. A-layer i is vertices i*G.., B-layer j is (k+j)*G.."""
    E = set()
    for i, j, s in darts:
        for x in range(G):
            E.add((i * G + x, (k + j) * G + int(T[x, s])))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Structured candidates for D = 3.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                try:
                    consider(*lib.projective_plane_incidence(q))
                except Exception:
                    pass
                break
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Main search: multi-base lifts over semidirect products, aiming above the best order.
    try:
        while best_n < moore and time.monotonic() < deadline:
            k = rng.choice((1, 2, 2, 3))
            target = best_n + 2
            Gmin = max(d, (target + 2 * k - 1) // (2 * k))
            G = Gmin + rng.randrange(0, max(2, Gmin // 25) + 1)
            if 2 * k * G > moore or 2 * k * G > MAX_V:
                continue
            groups = _groups(G)
            if not groups:
                continue
            rng.shuffle(groups)
            for m, k2, r in groups[:GROUPS_PER_G]:
                if time.monotonic() > deadline:
                    break
                T, invs = _table(m, k2, r)
                res = _anneal(d, D, k, G, T, invs, rng, deadline, ITERS)
                if res is not None:
                    n, e = _edges(k, G, T, res)
                    consider(n, e)
                    break
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
