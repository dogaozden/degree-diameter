"""Bold variant for (d, D) = (10, 5): 2-by-2 fibre voltage lifts over metacyclic groups.

Base graph: A-fibres A_0, A_1 and B-fibres B_0, B_1, each a copy of G.  Dart block (i, j) carries
c_ij darts with pairwise distinct voltages s, joining (A_i, x) to (B_j, x*s).  With
c = [[k, d-k], [d-k, k]] the lift is simple and d-regular with 4|G| vertices.  Left multiplication
by G is an automorphism that fixes the fibres, so the diameter is at most D iff BFS from the four
fibre identities reaches every vertex within D steps.  Annealing acts on the voltages (best of K
proposals, Metropolis acceptance, restarts when stuck).  Any cost-0 lift is checked with lib.is_valid.
Fallback: the parent's valid Haar graph (3582 vertices).  Other cases get the small trivial graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
DIAM = 5
K_PROPOSALS = 8
TEMP = 2.0
PATIENCE = 3000
SLICE = 2.0
POOL = 5
ORDER_LO, ORDER_HI = 897, 1080


# ----------------------------------------------------------------------------- groups

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> index a*k + j, identity = 0.  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def candidates(lo, hi):
    """Metacyclic groups of order in [lo, hi], largest order first (up to 2 per order)."""
    out = []
    for order in range(hi, lo - 1, -1):
        got = 0
        for k in range(2, order // 2 + 1):
            if order % k:
                continue
            m = order // k
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((m, k, lam))
                    got += 1
                    break
            if got >= 2:
                break
    return out


# ------------------------------------------------------------------ lift construction

def haar_edges(MT, S):
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def lift_nbr(MT, inv, N, d, blocks):
    """Neighbour array (4N x d) of the lift.  Fibres: A_0 = [0,N), A_1 = [N,2N), B_0 = [2N,3N), B_1 = [3N,4N).
    blocks[b] holds the voltages of dart block b = (i, j), i = b // 2, j = b % 2.
    Returns None if the row or column degrees are not exactly d."""
    nbr = np.empty((4 * N, d), dtype=np.int64)
    colA = [0, 0]
    colB = [0, 0]
    for b, vs in enumerate(blocks):
        i, j = b // 2, b % 2
        for s in vs:
            ca, cb = colA[i], colB[j]
            if ca >= d or cb >= d:
                return None
            nbr[i * N:(i + 1) * N, ca] = (2 + j) * N + MT[:, s]
            nbr[(2 + j) * N:(3 + j) * N, cb] = i * N + MT[:, inv[s]]
            colA[i] += 1
            colB[j] += 1
    if colA != [d, d] or colB != [d, d]:
        return None
    return nbr


def lift_cost(nbr, N, D):
    """Total number of vertices not reached within D steps from the four fibre identities."""
    n = nbr.shape[0]
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(D):
            nx = nbr[fr].ravel()
            nx = np.unique(nx[~seen[nx]])
            if nx.size == 0:
                break
            seen[nx] = True
            fr = nx
        total += n - int(seen.sum())
    return total


def lift_graph(nbr):
    n = nbr.shape[0]
    rows = nbr[: n // 2].tolist()
    edges = [(u, v) for u, row in enumerate(rows) for v in row]
    return n, edges


# ------------------------------------------------------------------------- search

def random_blocks(N, counts, rng):
    return [[int(x) for x in rng.choice(N, c, replace=False)] for c in counts]


def propose(blocks, counts, N, rng):
    b = int(rng.integers(4))
    if counts[b] == 0:
        return None
    t = int(rng.integers(counts[b]))
    x = int(rng.integers(N))
    if x in blocks[b]:
        return None
    nb = [list(v) for v in blocks]
    nb[b][t] = x
    return nb


def restart(st, d, rng):
    N, counts = st['N'], st['counts']
    st['blocks'] = random_blocks(N, counts, rng)
    nbr = lift_nbr(st['MT'], st['inv'], N, d, st['blocks'])
    st['cur'] = lift_cost(nbr, N, DIAM)
    st['best'], st['since'] = st['cur'], 0


def make_state(spec, d, rng):
    m, k, lam = spec
    MT, inv = group_meta(m, k, lam)
    N = m * k
    kk = [4, 5, 6][int(rng.integers(3))]
    counts = [kk, d - kk, d - kk, kk]
    st = {'N': N, 'MT': MT, 'inv': inv, 'counts': counts, 'order': N}
    st['blocks'] = random_blocks(N, counts, rng)
    nbr = lift_nbr(MT, inv, N, d, st['blocks'])
    st['cur'] = lift_cost(nbr, N, DIAM)
    st['best'], st['since'] = st['cur'], 0
    return st


def anneal(st, d, end, rng):
    """Anneal the voltages of one group until `end`.  Returns a checked (n, edges) or None."""
    N, MT, inv, counts = st['N'], st['MT'], st['inv'], st['counts']
    while time.monotonic() < end:
        cands = []
        for _ in range(K_PROPOSALS):
            p = propose(st['blocks'], counts, N, rng)
            if p is None:
                continue
            nbr = lift_nbr(MT, inv, N, d, p)
            if nbr is None:
                continue
            cands.append((lift_cost(nbr, N, DIAM), p, nbr))
        if not cands:
            continue
        cands.sort(key=lambda t: t[0])
        c, p, nbr = cands[0]
        delta = c - st['cur']
        if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
            st['blocks'], st['cur'] = p, c
            if c < st['best']:
                st['best'], st['since'] = c, 0
            else:
                st['since'] += 1
            if c == 0:
                n, edges = lift_graph(nbr)
                if lib.is_valid(n, edges, d, DIAM):
                    return n, edges
                restart(st, d, rng)
                continue
        else:
            st['since'] += 1
        if st['since'] > PATIENCE:
            restart(st, d, rng)
    return None


# ------------------------------------------------------------------------ fallback

# Valid Haar graph on 2 * 1791 = 3582 vertices, checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


# -------------------------------------------------------------------------- entry

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    deadline = t0 + 0.70 * time_limit
    rng = np.random.default_rng(seed)
    cands = candidates(ORDER_LO, ORDER_HI)

    # best_order: a lift on 4|G| vertices beats the fallback (3582) once |G| >= 896.
    best = None
    best_order = 895
    pool = []
    idx = 0

    def fill():
        nonlocal idx
        while len(pool) < POOL and idx < len(cands):
            spec = cands[idx]
            idx += 1
            if spec[0] * spec[1] <= best_order:
                continue
            try:
                pool.append(make_state(spec, d, rng))
            except Exception:
                pass

    try:
        fill()
        while pool and time.monotonic() < deadline:
            for st in list(pool):
                if time.monotonic() >= deadline:
                    break
                if st['order'] <= best_order:
                    pool.remove(st)
                    continue
                try:
                    res = anneal(st, d, min(deadline, time.monotonic() + SLICE), rng)
                except Exception:
                    pool.remove(st)
                    continue
                if res is not None:
                    best = res
                    best_order = res[0] // 4
                    pool[:] = [s for s in pool if s['order'] > best_order]
            pool[:] = [s for s in pool if s['order'] > best_order]
            fill()
    except Exception:
        pass

    if best is not None:
        return best

    try:
        MT, inv = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
