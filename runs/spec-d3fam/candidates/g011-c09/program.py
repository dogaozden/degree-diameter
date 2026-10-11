import math
import random
import time

import numpy as np

import lib

TIME_FRAC = 0.85      # fraction of time_limit used before returning
MARGIN = 2.0          # seconds kept in reserve
ITER = 2500           # annealing steps per growth attempt
T0 = 1.5              # initial annealing temperature
MAX_FAILS = 6         # consecutive failed growth attempts before stopping


# ---------------------------------------------------------------- helpers

def _two_colour(n, edges):
    """Proper 2-colouring of a bipartite graph, component by component."""
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
    return color


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _matrix_from_graph(n, edges, color):
    """Biadjacency matrix: rows = colour-0 vertices, columns = colour-1 vertices, in index order."""
    rows = [v for v in range(n) if color[v] == 0]
    cols = [v for v in range(n) if color[v] == 1]
    rp = {v: i for i, v in enumerate(rows)}
    cp = {v: j for j, v in enumerate(cols)}
    M = np.zeros((len(rows), len(cols)), dtype=np.int8)
    for u, v in edges:
        if color[u] == 0:
            M[rp[u], cp[v]] = 1
        else:
            M[rp[v], cp[u]] = 1
    return M


def _edges_from(M):
    """Edge list with rows as vertices 0..na-1 and columns as vertices na..na+nb-1."""
    na = M.shape[0]
    ii, jj = np.nonzero(M)
    return [(int(i), na + int(j)) for i, j in zip(ii, jj)]


# ------------------------------------------------- matrix-product cost (new)

def _cost(M):
    """Exact count of defects for diameter 3 in a bipartite graph given by its biadjacency M.

    Same-side pairs need a common neighbour (distance <= 2). A non-adjacent cross pair
    (a, b) needs a path a-b'-a'-b, i.e. (M M^T M)[a, b] > 0. All three are matrix products,
    so one evaluation costs a few small BLAS calls instead of a Python BFS.
    """
    Mf = M.astype(np.float32)
    P = Mf @ Mf.T              # common neighbours of row pairs
    R = Mf.T @ Mf              # common neighbours of column pairs
    Q = P @ Mf                 # walks a-b'-a'-b
    zp = P < 0.5
    np.fill_diagonal(zp, False)
    zr = R < 0.5
    np.fill_diagonal(zr, False)
    zc = (Mf < 0.5) & (Q < 0.5)
    return int(zp.sum()) + int(zr.sum()) + int(zc.sum())


def _anneal(M, deadline, rng):
    """Degree-preserving double-edge swaps driven by _cost. Returns M (cost 0) or None."""
    nc = M.shape[1]
    cost = _cost(M)
    for it in range(ITER):
        if cost == 0:
            break
        if time.monotonic() > deadline:
            return None
        idx = np.flatnonzero(M)
        if len(idx) < 2:
            return None
        a = int(idx[rng.randrange(len(idx))])
        b = int(idx[rng.randrange(len(idx))])
        i, j = divmod(a, nc)
        k, l = divmod(b, nc)
        if i == k or j == l:
            continue
        if M[i, l] or M[k, j]:
            continue
        M[i, j] = 0
        M[k, l] = 0
        M[i, l] = 1
        M[k, j] = 1
        new = _cost(M)
        delta = new - cost
        temp = T0 * (1.0 - it / ITER) + 0.05
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / temp)):
            cost = new
        else:
            M[i, j] = 1
            M[k, l] = 1
            M[i, l] = 0
            M[k, j] = 0
    return M if cost == 0 else None


def _augment(M, d, rng):
    """Add edges between deficient opposite-side vertices; distances can only shrink."""
    na, nb = M.shape
    rd = M.sum(axis=1).tolist()
    cd = M.sum(axis=0).tolist()
    rows = [i for i in range(na) if rd[i] < d]
    cols = [j for j in range(nb) if cd[j] < d]
    rng.shuffle(rows)
    for i in rows:
        if rd[i] >= d:
            continue
        for j in cols:
            if rd[i] >= d:
                break
            if cd[j] < d and M[i, j] == 0:
                M[i, j] = 1
                rd[i] += 1
                cd[j] += 1


def _attempt(M, d, deadline, rng, nrng):
    """Add one vertex on a random side (greedy cover of the other side), then anneal."""
    c = rng.randrange(2)
    A = (M if c == 0 else M.T).astype(np.int8)   # rows = side c, new vertex is a new row
    na, nb = A.shape

    # Greedy cover: pick <= d neighbours on the other side covering all rows' pairs.
    covered = np.zeros(na, dtype=bool)
    chosen = []
    for _ in range(d):
        if covered.all():
            break
        gains = A[~covered].sum(axis=0).astype(np.float64) + 0.5 * nrng.random(nb)
        if chosen:
            gains[np.array(chosen, dtype=np.int64)] = -1e9
        j = int(np.argmax(gains))
        chosen.append(j)
        covered |= A[:, j].astype(bool)

    colsum = A.sum(axis=0)
    B = np.vstack([A, np.zeros((1, nb), dtype=np.int8)])
    # Free a slot on saturated neighbours.
    for j in chosen:
        if colsum[j] >= d:
            rows = np.flatnonzero(B[:na, j])
            i = int(rows[rng.randrange(len(rows))])
            B[i, j] = 0
    for j in chosen:
        B[na, j] = 1

    Mn = np.ascontiguousarray(B if c == 0 else B.T, dtype=np.int8)
    Mn = _anneal(Mn, deadline, rng)
    if Mn is None:
        return None
    _augment(Mn, d, rng)
    return Mn


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)
    nrng = np.random.default_rng(seed & 0x7FFFFFFF)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                       # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                       # K_{d,d} is extremal for D = 2
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):   # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    # Starting candidates (all verified with lib.is_valid).
    bases = []
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            bases.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    pg = _pg_base(d)
    if pg is not None:
        bases.append(pg)
    kdd = lib.haar_graph(d, range(d))
    bases.append(kdd)
    valid = [(n, e) for n, e in bases if lib.is_valid(n, e, d, D)]
    if not valid:
        return kdd
    base_n, base_e = max(valid, key=lambda c: c[0])

    if D != 3:
        return base_n, base_e

    # Growth search on the biadjacency matrix with matrix-product cost.
    try:
        color = _two_colour(base_n, base_e)
        M = _matrix_from_graph(base_n, base_e, color)
    except Exception:
        return base_n, base_e

    best_n, best_e = base_n, base_e
    fails = 0
    while time.monotonic() < deadline and fails < MAX_FAILS:
        res = _attempt(M, d, deadline, rng, nrng)
        if res is None:
            fails += 1
            continue
        fails = 0
        M = res
        n = M.shape[0] + M.shape[1]
        if n > best_n:
            e = _edges_from(M)
            if lib.is_valid(n, e, d, D):
                best_n, best_e = n, e
            else:
                break

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return base_n, base_e
