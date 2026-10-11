import random
import time

import numpy as np

import lib

TIME_FRAC = 0.85     # fraction of time_limit used before returning
MARGIN = 2.0         # seconds kept in reserve
STEPS = 3000         # breakout steps per growth attempt
CANDS = 6            # random double-edge swaps scored per step
MAX_FAILS = 6        # consecutive failed growth attempts before stopping


# ---------------------------------------------------------------- matrix helpers

def _reach(A, r):
    """0/1 matrix R with R[u, v] = 1 iff dist(u, v) <= r (boolean matrix power via float matmul)."""
    n = A.shape[0]
    M = A + np.eye(n, dtype=np.float32)
    R = np.eye(n, dtype=np.float32)
    for _ in range(r):
        R = ((R @ M) > 0).astype(np.float32)
    return R


def _bad(A, D):
    """Boolean matrix of pairs at distance > D (unreachable included). Diagonal is False."""
    return _reach(A, D) == 0


def _matrix(n, edges):
    A = np.zeros((n, n), np.float32)
    for u, v in edges:
        A[u, v] = 1
        A[v, u] = 1
    return A


def _edges_of(A):
    us, vs = np.nonzero(np.triu(A, 1))
    return [(int(u), int(v)) for u, v in zip(us, vs)]


def _colour(n, edges):
    """Proper 2-colouring of a bipartite graph (BFS per component)."""
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
    return np.array(color, dtype=np.int8)


# ---------------------------------------------------------------- moves

def _random_swap(A, s0, rng):
    """Degree-preserving double-edge swap between sides; returns a new matrix or None."""
    a1 = int(s0[rng.randrange(len(s0))])
    n1 = np.flatnonzero(A[a1])
    if len(n1) == 0:
        return None
    b1 = int(n1[rng.randrange(len(n1))])
    a2 = int(s0[rng.randrange(len(s0))])
    if a2 == a1:
        return None
    n2 = np.flatnonzero(A[a2])
    if len(n2) == 0:
        return None
    b2 = int(n2[rng.randrange(len(n2))])
    if b1 == b2 or A[a1, b2] or A[a2, b1]:
        return None
    B = A.copy()
    B[a1, b1] = B[b1, a1] = 0
    B[a2, b2] = B[b2, a2] = 0
    B[a1, b2] = B[b2, a1] = 1
    B[a2, b1] = B[b1, a2] = 1
    return B


def _anneal(A, color, D, rng, deadline):
    """Breakout local search: weighted bad-pair cost; weights of stuck pairs grow at local minima."""
    n = A.shape[0]
    s0 = np.flatnonzero(color == 0)
    W = np.ones((n, n), np.float32)
    np.fill_diagonal(W, 0)
    for _ in range(STEPS):
        if time.monotonic() > deadline:
            return None
        bad = _bad(A, D)
        if not bad.any():
            return A
        cur = float((W * bad).sum())
        best_cost, best_B = None, None
        for _ in range(CANDS):
            B = _random_swap(A, s0, rng)
            if B is None:
                continue
            c = float((W * _bad(B, D)).sum())
            if best_cost is None or c < best_cost:
                best_cost, best_B = c, B
        if best_B is not None and best_cost < cur:
            A = best_B
        else:
            W[bad] += 1.0
    return None


def _augment(A, color, d, nprng):
    """Add edges between deficient opposite-colour vertices. Adding edges never breaks the diameter bound."""
    deg = A.sum(1)
    d0 = np.flatnonzero((color == 0) & (deg < d))
    d1 = np.flatnonzero((color == 1) & (deg < d))
    for u in nprng.permutation(d0):
        for v in d1:
            if deg[u] >= d:
                break
            if deg[v] < d and A[u, v] == 0:
                A[u, v] = A[v, u] = 1
                deg[u] += 1
                deg[v] += 1
    return A


def _attempt(A, color, d, D, rng, nprng, deadline):
    """Add one vertex of random side, rewire to fix bad pairs. Returns (A, color) or None."""
    n = A.shape[0]
    c = rng.randrange(2)
    other = np.flatnonzero(color == 1 - c)
    if len(other) < d:
        return None

    # Greedy choice of d neighbours that cover the radius-(D-1) balls.
    balls = _reach(A, D - 1) > 0
    covered = np.zeros(n, bool)
    pool = other.copy()
    chosen = []
    while len(chosen) < d and len(pool) > 0:
        gains = (balls[pool] & ~covered).sum(1) + 0.5 * nprng.random(len(pool))
        i = int(np.argmax(gains))
        u = int(pool[i])
        chosen.append(u)
        covered |= balls[u]
        pool = np.delete(pool, i)

    B = np.zeros((n + 1, n + 1), np.float32)
    B[:n, :n] = A
    x = n
    for u in chosen:
        if B[u].sum() >= d:
            nb = np.flatnonzero(B[u])
            w = int(nb[rng.randrange(len(nb))])
            B[u, w] = B[w, u] = 0
        B[x, u] = B[u, x] = 1
    col = np.append(color, np.int8(c))

    res = _anneal(B, col, D, rng, deadline)
    if res is None:
        return None
    return _augment(res, col, d, nprng), col


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)
    nprng = np.random.default_rng(seed & 0xFFFFFFFF)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):   # Moore-extremal, cannot grow
        return lib.projective_plane_incidence(d - 1)

    bases = []
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            bases.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q >= 2:
        bases.append(lib.projective_plane_incidence(q))
    bases.append(lib.haar_graph(d, range(d)))
    valid = [(n, e) for n, e in bases if lib.is_valid(n, e, d, D)]
    if not valid:
        return lib.haar_graph(d, range(d))
    base_n, base_e = max(valid, key=lambda c: c[0])

    best_n, best_e = base_n, base_e
    cur_A = _matrix(base_n, base_e)
    cur_col = _colour(base_n, base_e)
    best_A = cur_A

    fails = 0
    while time.monotonic() < deadline and fails < MAX_FAILS:
        res = _attempt(cur_A, cur_col, d, D, rng, nprng, deadline)
        if res is None:
            fails += 1
            continue
        fails = 0
        cur_A, cur_col = res
        if cur_A.shape[0] > best_n:
            best_n = cur_A.shape[0]
            best_A = cur_A
            best_e = _edges_of(best_A)

    if best_n > base_n:
        cand_e = _edges_of(best_A)
        if lib.is_valid(best_n, cand_e, d, D):
            return best_n, cand_e
    return base_n, base_e
