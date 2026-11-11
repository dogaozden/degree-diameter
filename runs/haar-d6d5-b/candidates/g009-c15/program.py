"""Bi-Cayley and Haar search for the bipartite degree-diameter problem, d=6, D=5 (numpy only).

CONSTRUCTION 1 (Haar graphs, new stage).  Take a non-abelian metacyclic group G = Z_m x| Z_k of order N in
[331, 350] and a connection set S of 6 distinct elements.  Vertices A(g) and B(g), edges A(g) ~ B(g*s) for s in S.
This graph is 6-regular on 2N vertices.  Left multiplication is an automorphism that is transitive on each side,
so diameter <= 5 iff BFS of radius 5 from A(e) and from B(e) reaches every vertex.  Any N >= 331 beats the
parent's Haar fallback of order 660.  N = 342 ties the record 684, and N >= 343 beats it.

CONSTRUCTION 2 (bi-Cayley, unchanged from parent).  Four orbits with connection sets of sizes a, 6-a, 6-a, a.
Order N >= 172 gives 4N > 684 vertices.

Both searches use simulated annealing on the connection sets.  The cost is the number of vertices not reached
within 5 steps from the base vertices.  Every candidate is checked with lib.is_valid before it is returned.  If
nothing is found, a valid order-660 Haar graph (checked at run time) or a trivial valid graph is returned.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
MIN_N = 172   # 4 * 172 = 688 > 684 (record)


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) integer coordinate array (element 0 = identity) and a vectorised product."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sorted_codes = codes[order]
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sorted_codes, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------------- Haar fallback helpers

def checked(MT, S, d, D):
    """The Haar graph for S (edges A(g) ~ B(g*s)), or None if it is not exactly valid."""
    N = MT.shape[0]
    edges = [(g, N + int(MT[g, s])) for g in range(N) for s in S]
    return (2 * N, edges) if lib.is_valid(2 * N, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _fallback(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked), else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        g = checked(MT, [0, 179, 116, 180, 47, 306], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------------------ Haar search (stage 1)

def _haar_candidates():
    """One non-abelian metacyclic group per order N in [331, 350] that is composite, smallest orders first."""
    out = []
    for NN in range(331, 351):
        for k in range(2, NN // 3 + 1):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            lam = next((l for l in range(2, m)
                        if math.gcd(l, m) == 1 and pow(l, k, m) == 1), None)
            if lam is not None:
                out.append((m, k, lam))
                break
    return out[:10]


def _haar_nbr(MT, inv, S):
    """Neighbour array (2N x DEG): A-vertex g -> B(g*s), B-vertex g -> A(g*s^-1)."""
    nA = MT[:, S].astype(np.int64) + MT.shape[0]
    nB = MT[:, inv[S]].astype(np.int64)
    return np.vstack([nA, nB])


def _haar_cost(nbr, N):
    """Vertices not reached within DIAM steps from A(e) and B(e) (0 means valid)."""
    n2 = 2 * N
    total = 0
    for src in (0, N):
        seen = np.zeros(n2, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(DIAM):
            nx = np.unique(nbr[fr].ravel())
            nx = nx[~seen[nx]]
            if nx.size == 0:
                break
            seen[nx] = True
            fr = nx
        total += n2 - int(np.count_nonzero(seen))
    return total


def _haar_search(MT, inv, deadline, rng):
    """Anneal a 6-element set S until the Haar graph has diameter <= DIAM; return checked (n, edges) or None."""
    N = MT.shape[0]
    while time.monotonic() < deadline:
        S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
        cur = _haar_cost(_haar_nbr(MT, inv, S), N)
        stall = 0
        T = 0.5
        while time.monotonic() < deadline and cur > 0 and stall < 3000:
            pos = int(rng.integers(DEG))
            x = int(rng.integers(N))
            if np.any(S == x):
                stall += 1
                continue
            newS = S.copy()
            newS[pos] = x
            c = _haar_cost(_haar_nbr(MT, inv, newS), N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            edges = [(g, N + int(MT[g, int(s)])) for g in range(N) for s in S]
            if lib.is_valid(2 * N, edges, DEG, DIAM):
                return 2 * N, edges
    return None


def _haar_stage(deadline, rng):
    """Run the Haar search over the candidate groups; return the largest checked graph found, or None."""
    cands = _haar_candidates()
    best = None
    for idx, (m, k, lam) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
            res = _haar_search(MT, inv, end, rng)
        except Exception:
            continue
        if res is not None and (best is None or res[0] > best[0]):
            best = res
    return best


# ------------------------------------------------------------------------- bi-Cayley graph and cost

def _candidates():
    """Non-abelian metacyclic groups of order in [MIN_N, 200], plus Heis(3) x Z_7 (order 189)."""
    out = []
    for NN in range(MIN_N, 201):
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and pow(lam, 1, m) != 1:
                    out.append(("meta", m, k, lam))
                    break
    out = out[:8]
    out.append(("heis", 3, 7, 0))
    return out


def _make(c):
    if c[0] == "meta":
        return group_meta(c[1], c[2], c[3])
    return group_times_cyclic(group_heis(c[1]), c[2])


def _nbr(MT, inv, N, S):
    """Neighbour array (4N x DEG).  Orbits: A_0 = 0..N-1, A_1 = N..2N-1, B_0 = 2N..3N-1, B_1 = 3N..4N-1.
    A_i(g) ~ B_j(g*s) for s in S[(i, j)]."""
    g = np.arange(N, dtype=np.int64)
    nbr = np.empty((4 * N, DEG), dtype=np.int64)
    for i in (0, 1):
        c = 0
        for j in (0, 1):
            for s in S[(i, j)]:
                nbr[i * N:(i + 1) * N, c] = (2 + j) * N + MT[g, s]
                c += 1
    for j in (0, 1):
        c = 0
        for i in (0, 1):
            for s in S[(i, j)]:
                nbr[(2 + j) * N:(3 + j) * N, c] = i * N + MT[g, inv[s]]
                c += 1
    return nbr


def _cost(nbr, N):
    """Vertices not reached within DIAM steps from the four base vertices (0 means diameter <= DIAM)."""
    n = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(DIAM):
            nx = nbr[fr].ravel()
            nx = np.unique(nx[~seen[nx]])
            if nx.size == 0:
                break
            seen[nx] = True
            fr = nx
        total += n - int(np.count_nonzero(seen))
    return total


def _search(MT, inv, N, deadline, rng):
    """Anneal the four connection sets until cost 0; return a checked (n, edges) or None."""
    while time.monotonic() < deadline:
        a = int(rng.choice([2, 3, 3, 4]))
        sizes = {(0, 0): a, (0, 1): DEG - a, (1, 0): DEG - a, (1, 1): a}
        keys = list(sizes)
        S = {k: rng.choice(N, size=sizes[k], replace=False).astype(np.int64) for k in keys}
        cur = _cost(_nbr(MT, inv, N, S), N)
        stall = 0
        T = 0.6
        while time.monotonic() < deadline and cur > 0 and stall < 4000:
            key = keys[int(rng.integers(4))]
            pos = int(rng.integers(sizes[key]))
            x = int(rng.integers(N))
            if x in S[key]:
                stall += 1
                continue
            newS = dict(S)
            arr = S[key].copy()
            arr[pos] = x
            newS[key] = arr
            c = _cost(_nbr(MT, inv, N, newS), N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            nbr = _nbr(MT, inv, N, S)
            n = 4 * N
            edges = [(u, int(v)) for u in range(2 * N) for v in nbr[u]]
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


# --------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    # Stage 1: Haar graphs over groups of order 331..350 (beats the 660 fallback as soon as found).
    best = _haar_stage(t0 + 0.5 * budget, rng)

    # Stage 2: bi-Cayley search with the remaining time (order 4N >= 688 would beat the record).
    cands = _candidates()
    for idx, c in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = _make(c)
            N = MT.shape[0]
            g = _search(MT, inv, N, end, rng)
        except Exception:
            continue
        if g is not None and (best is None or g[0] > best[0]):
            best = g

    if best is not None:
        return best
    return _fallback(d, D)
