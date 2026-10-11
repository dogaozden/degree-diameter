import math
import random
import time

import numpy as np

import lib

ITERS = 800


def _colors(n, adj):
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


def _state_from_edges(n, edges, d):
    """Regular bipartite graph -> (nbr, M, E, n); returns None if not d-regular or not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d for a in adj):
        return None
    color = _colors(n, adj)
    for u, v in edges:
        if color[u] == color[v]:
            return None
    nbr = np.array(adj, dtype=np.int64)
    M = np.zeros((n, n), dtype=bool)
    for u, v in edges:
        M[u, v] = True
        M[v, u] = True
    E = [((u, v) if color[u] == 0 else (v, u)) for u, v in edges]
    E = [(int(a), int(b)) for a, b in E]
    return nbr, M, E, n


def _rep(nbr, x, old, new):
    k = int(np.flatnonzero(nbr[x] == old)[0])
    nbr[x, k] = new


def _cost(nbr, D):
    """Ordered pairs at distance > D, bit-parallel over numpy uint64 words."""
    n = nbr.shape[0]
    W = (n + 63) // 64
    R = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n)
    R[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        R = R | np.bitwise_or.reduce(R[nbr], axis=1)
    cnt = int(np.unpackbits(R.view(np.uint8)).sum())
    return n * n - cnt


def _anneal(nbr, M, E, D, rng, deadline, iters):
    """Degree-preserving double-edge swaps minimising bad ordered pairs. Mutates nbr, M, E."""
    cost = _cost(nbr, D)
    T = 0.5
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.998)
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or M[a, e] or M[c, b]:
            continue
        _rep(nbr, a, b, e)
        _rep(nbr, b, a, c)
        _rep(nbr, c, e, b)
        _rep(nbr, e, c, a)
        M[a, b] = M[b, a] = False
        M[c, e] = M[e, c] = False
        M[a, e] = M[e, a] = True
        M[c, b] = M[b, c] = True
        new = _cost(nbr, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            _rep(nbr, a, e, b)
            _rep(nbr, b, c, a)
            _rep(nbr, c, b, e)
            _rep(nbr, e, a, c)
            M[a, e] = M[e, a] = False
            M[c, b] = M[b, c] = False
            M[a, b] = M[b, a] = True
            M[c, e] = M[e, c] = True
    return cost


def _pair_insert(st, d, rng):
    """Add an adjacent (left a, right b) pair keeping d-regularity: remove d-1 matched edges (x_i, y_i),
    join a to every y_i, b to every x_i, and a-b. Returns a fresh state or None."""
    nbr, M, E, n = st
    order = list(range(len(E)))
    rng.shuffle(order)
    usedL, usedR, pick = set(), set(), []
    for k in order:
        x, y = E[k]
        if x in usedL or y in usedR:
            continue
        usedL.add(x)
        usedR.add(y)
        pick.append(k)
        if len(pick) == d - 1:
            break
    if len(pick) < d - 1:
        return None
    a, b = n, n + 1
    nbr2 = np.zeros((n + 2, d), dtype=np.int64)
    nbr2[:n] = nbr
    M2 = np.zeros((n + 2, n + 2), dtype=bool)
    M2[:n, :n] = M
    pickset = set(pick)
    E2 = [E[k] for k in range(len(E)) if k not in pickset]
    xs, ys = [], []
    for k in pick:
        x, y = E[k]
        _rep(nbr2, x, y, b)
        _rep(nbr2, y, x, a)
        xs.append(x)
        ys.append(y)
        M2[x, y] = M2[y, x] = False
        M2[x, b] = M2[b, x] = True
        M2[a, y] = M2[y, a] = True
        E2.append((x, b))
        E2.append((a, y))
    nbr2[a, :d - 1] = ys
    nbr2[a, d - 1] = b
    nbr2[b, :d - 1] = xs
    nbr2[b, d - 1] = a
    M2[a, b] = M2[b, a] = True
    E2.append((a, b))
    return nbr2, M2, E2, n + 2


def _grow(st, d, D, deadline, rng, consider):
    """Adaptive batched pair growth: each batch of pairs is annealed; success keeps it."""
    batch, fails = 1, 0
    while time.monotonic() < deadline and fails < 12:
        cand, steps = st, 0
        for _ in range(batch):
            nxt = _pair_insert(cand, d, rng)
            if nxt is None:
                break
            cand = nxt
            steps += 1
        if steps == 0:
            break
        cost = _anneal(cand[0], cand[1], cand[2], D, rng, deadline, ITERS)
        if cost == 0:
            st = cand
            consider(cand[3], list(cand[2]))
            batch = min(batch * 2, 16)
            fails = 0
        else:
            batch = max(1, batch // 2)
            fails += 1
    return st


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.82 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    best_n, best_e = fallback[0], list(fallback[1])

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D < 3:
        return best_n, best_e

    seeds = [lib.haar_graph(d, range(d))]
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            seeds.append(lib.projective_plane_incidence(q))
            break
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            seeds.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    states = []
    for n, e in seeds:
        consider(n, e)
        st = _state_from_edges(n, e, d)
        if st is not None:
            states.append((n, st))
    states.sort(key=lambda t: -t[0])
    states = [st for _, st in states]

    for idx, st in enumerate(states):
        now = time.monotonic()
        share = (deadline - now) / (len(states) - idx)
        if share <= 0:
            break
        _grow(st, d, D, now + share, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = fallback[0], list(fallback[1])
    return best_n, best_e
