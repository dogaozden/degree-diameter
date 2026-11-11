"""Multi-orbit voltage lifts for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  Take a metacyclic group G = Z_m x|_r Z_k (order N) and a circulant base pattern with p
A-vertices and p B-vertices.  Base multiplicities M[i][j] = w[(j-i) mod p], with w a composition of d into p
positive parts.  Vertices are (i, x) and (j, y), x, y in G.  Each base dart (i, j, g) gives edges
(i, x) ~ (j, g*x).  Left multiplication by G is an automorphism, so every vertex lies in a G-orbit per base vertex.
Hence the graph has diameter <= D iff, for each of the 2p base vertices, the ball of radius D around (base, e)
covers all 2pN vertices.  Each dart block has distinct voltages, so the graph is simple and d-regular.

SEARCH.  Simulated annealing on the voltages, with cost = number of (source, vertex) pairs not reached.  Several
such searches run round-robin.  Any zero-cost configuration is checked with lib.is_valid before it is accepted.
A valid Haar graph (2*1791 = 3582 vertices) is the safe fallback, so the output is never worse than the parent's.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10
POOL = 5

# Valid Haar fallback from the parent (group Z_199 x| Z_9, 1791 elements, 3582 vertices).
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------ groups

def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l).  Returns (MT, inv)."""
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    ak = idx // k
    jk = idx % k
    MT = np.empty((N, N), dtype=np.int32)
    step = 128
    for lo in range(0, N, step):
        hi = min(N, lo + step)
        a = ak[lo:hi, None]
        j = jk[lo:hi, None]
        MT[lo:hi] = ((a + pw[j] * ak[None, :]) % m) * k + (j + jk[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def random_group(N, rng):
    """A random metacyclic group of order N, non-abelian when possible."""
    cands = [(m, N // m) for m in range(2, N) if N % m == 0 and N // m >= 2]
    if not cands:
        return group_table(1, N, 1)  # cyclic
    m, k = cands[int(rng.integers(len(cands)))]
    rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    r = rs[int(rng.integers(len(rs)))] if rs else 1
    return group_table(m, k, r)


def compositions(total, parts):
    """All ways to write total as an ordered sum of `parts` positive integers."""
    if parts == 1:
        return [(total,)]
    out = []
    for a in range(1, total - parts + 2):
        for rest in compositions(total - a, parts - 1):
            out.append((a,) + rest)
    return out


COMPS = {p: compositions(TARGET_D, p) for p in range(1, 5)}


# ------------------------------------------------------------------------------ lift

def layout(p, w):
    """Dart layout for the circulant base: darts t with row i, column j, and slot positions."""
    di, dj = [], []
    for i in range(p):
        for j in range(p):
            for _ in range(w[(j - i) % p]):
                di.append(i)
                dj.append(j)
    T = len(di)
    colA = [0] * T
    colB = [0] * T
    cnt = [0] * p
    for t in range(T):
        colA[t] = cnt[di[t]]
        cnt[di[t]] += 1
    cnt = [0] * p
    for t in range(T):
        colB[t] = cnt[dj[t]]
        cnt[dj[t]] += 1
    di_a = np.array(di, dtype=np.int64)
    dj_a = np.array(dj, dtype=np.int64)
    blocks_of = []
    for t in range(T):
        blocks_of.append(np.nonzero((di_a == di[t]) & (dj_a == dj[t]))[0])
    return di_a, dj_a, colA, colB, blocks_of


def cost_of(adj, p, N, D):
    """Number of (source, vertex) pairs at distance > D; sources are the 2p base-vertex identities."""
    n = adj.shape[0]
    S = 2 * p
    src = [i * N for i in range(p)] + [(p + j) * N for j in range(p)]
    reach = np.zeros((S, n), dtype=bool)
    reach[np.arange(S), src] = True
    for _ in range(D):
        reach = reach | reach[:, adj].any(axis=2)
    return S * n - int(np.count_nonzero(reach))


def edges_from_adj(adj):
    n, d = adj.shape
    src = np.repeat(np.arange(n, dtype=np.int64), d)
    dst = adj.ravel()
    mask = src < dst
    return list(zip(src[mask].tolist(), dst[mask].tolist()))


def anneal_gen(p, w, N, MT, inv, d, D, rng):
    """Generator: one annealing step per yield.  Yields ('found', adj) at cost 0, then ends."""
    di, dj, colA, colB, blocks_of = layout(p, w)
    T = len(di)
    n = 2 * p * N

    def set_dart(adj, t, g):
        i = int(di[t])
        j = int(dj[t])
        adj[i * N:(i + 1) * N, colA[t]] = p * N + j * N + MT[g]
        adj[(p + j) * N:(p + j + 1) * N, colB[t]] = i * N + MT[inv[g]]

    while True:
        dg = np.zeros(T, dtype=np.int64)
        for i in range(p):
            for j in range(p):
                ts = np.nonzero((di == i) & (dj == j))[0]
                if len(ts):
                    dg[ts] = rng.choice(N, len(ts), replace=False)
        adj = np.empty((n, d), dtype=np.int64)
        for t in range(T):
            set_dart(adj, t, int(dg[t]))
        cur = cost_of(adj, p, N, D)
        if cur == 0:
            yield ('found', adj.copy())
            return
        L = 3000
        for step in range(L):
            t = int(rng.integers(T))
            taken = dg[blocks_of[t]]
            g_new = int(rng.integers(N))
            if np.any(taken == g_new):
                yield None
                continue
            g_old = int(dg[t])
            set_dart(adj, t, g_new)
            dg[t] = g_new
            c = cost_of(adj, p, N, D)
            temp = 0.3 + 1.7 * (1.0 - step / L)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
                if cur == 0:
                    yield ('found', adj.copy())
                    return
            else:
                set_dart(adj, t, g_old)
                dg[t] = g_old
            yield None


def spawn(best_n, rng, d, D):
    """A fresh search task whose graph has more than best_n vertices."""
    p = int(rng.integers(1, 5))
    lo = best_n // (2 * p) + 1
    hi = (best_n + 900) // (2 * p)
    if hi < lo:
        hi = lo
    N = int(rng.integers(lo, hi + 1))
    w = COMPS[p][int(rng.integers(len(COMPS[p])))]
    MT, inv = random_group(N, rng)
    gen = anneal_gen(p, w, N, MT, inv, d, D, rng)
    return {'gen': gen, 'n': 2 * p * N}


def haar_from(MT, S, N):
    """Haar graph of the table group: (g, A) ~ (s*g, B), vertices A = g, B = N + g."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(S)):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


# ------------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.80 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        n, e = haar_from(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    pool = [spawn(best_n, rng, d, D) for _ in range(POOL)]
    while time.monotonic() < deadline:
        for idx in range(len(pool)):
            if time.monotonic() >= deadline:
                break
            task = pool[idx]
            if task['n'] <= best_n:
                pool[idx] = spawn(best_n, rng, d, D)
                continue
            try:
                out = next(task['gen'])
            except StopIteration:
                pool[idx] = spawn(best_n, rng, d, D)
                continue
            except Exception:
                pool[idx] = spawn(best_n, rng, d, D)
                continue
            if out is not None:
                n = task['n']
                edges = edges_from_adj(out[1])
                try:
                    ok = n > best_n and lib.is_valid(n, edges, d, D)
                except Exception:
                    ok = False
                if ok:
                    best_n, best_edges = n, edges
                pool[idx] = spawn(best_n, rng, d, D)

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
