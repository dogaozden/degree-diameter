import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k with a numpy-vectorised reachability cost.
# The lift has vertices A_x, B_x (x in G, |G| = N) with A_x ~ B_{x s} for s in S,
# so every vertex has degree |S| = d. Connection sets S are searched by
# simulated annealing on the number of vertex pairs farther than D apart.
# ----------------------------------------------------------------------------

WINDOW = 8            # candidate orders N just above the current lower bound
MAX_GROUPS = 12       # groups tried per order N
SA_ITERS = 2500       # annealing steps per group
GROUP_TIME = 4.0      # seconds spent on one group before moving on


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


def _tables(m, k, r):
    """Multiplication table T[x, g] = x*g and inverse table for Z_m x|_r Z_k (element (a,b) coded a*k+b)."""
    N = m * k
    X = np.arange(N, dtype=np.int64)
    a = X // k
    b = X % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    T = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    nb = (-b) % k
    invs = ((-pw[nb] * a) % m) * k + nb
    return T, invs


def _cost(N, T, S, D):
    """Number of (source, vertex) pairs not within distance D, for sources A_0 and B_0. Zero means valid."""
    Sarr = np.array(S, dtype=np.int64)
    Sinv = _INVS_CUR[Sarr]
    total = 0
    for src in (0, N):
        seen_a = np.zeros(N, dtype=bool)
        seen_b = np.zeros(N, dtype=bool)
        if src < N:
            seen_a[src] = True
            fa = seen_a.copy()
            fb = np.zeros(N, dtype=bool)
        else:
            seen_b[src - N] = True
            fb = seen_b.copy()
            fa = np.zeros(N, dtype=bool)
        for _ in range(D):
            if not (fa.any() or fb.any()):
                break
            nb = np.zeros(N, dtype=bool)
            xs = np.flatnonzero(fa)
            if xs.size:
                nb[T[np.ix_(xs, Sarr)].ravel()] = True
            nb &= ~seen_b
            ys = np.flatnonzero(fb)
            na = np.zeros(N, dtype=bool)
            if ys.size:
                na[T[np.ix_(ys, Sinv)].ravel()] = True
            na &= ~seen_a
            seen_a |= na
            seen_b |= nb
            fa, fb = na, nb
        total += 2 * N - int(seen_a.sum()) - int(seen_b.sum())
    return total


_INVS_CUR = None  # inverse table of the group currently being searched


def _anneal(d, D, N, T, invs, rng, deadline, iters):
    """Simulated annealing over connection sets S (identity fixed in S WLOG). Returns S with cost 0, or None."""
    global _INVS_CUR
    _INVS_CUR = invs
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cost(N, T, S, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _cost(N, T, S2, D)
        delta = v - cur
        temp = 2.0 * (1.0 - it / iters) + 0.05
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / temp)):
            S, cur = S2, v
    return S if cur == 0 else None


def _lift_edges(N, T, S):
    Tl = T.tolist()
    return [(x, N + Tl[x][s]) for x in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        # Structured baselines for D = 3.
        if D == 3:
            for q in range(d - 1, 1, -1):
                if lib.is_prime_power(q):
                    n, e = lib.projective_plane_incidence(q)
                    consider(n, e)
                    break
            if d >= 5 and d - 2 >= 3 and lib.is_prime_power(d - 2):
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)

        # Main search: Bi-Cayley lifts with order N just above the current record.
        while best[0] < moore and time.monotonic() < deadline:
            lo = best[0] // 2 + 1
            if lo > moore // 2:
                break
            N = lo + rng.randrange(WINDOW)
            if N - 1 < d - 1:
                continue
            groups = _groups(N)
            rng.shuffle(groups)
            found = None
            for m, k, r in groups[:MAX_GROUPS]:
                now = time.monotonic()
                if now >= deadline:
                    break
                T, invs = _tables(m, k, r)
                global_invs = invs
                gdead = min(deadline, now + GROUP_TIME)
                S = _anneal_wrapper(d, D, N, T, invs, rng, gdead, SA_ITERS)
                if S is not None:
                    found = (T, S)
                    break
            if found is not None:
                T, S = found
                consider(2 * N, _lift_edges(N, T, S))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


def _anneal_wrapper(d, D, N, T, invs, rng, deadline, iters):
    """Set the inverse table for the cost function, then run annealing."""
    return _anneal(d, D, N, T, invs, rng, deadline, iters)
