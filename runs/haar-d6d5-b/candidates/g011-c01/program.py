"""Search for bipartite degree-diameter graphs, d=6, D=5 (numpy only).

Two constructions are searched, in order, within the time budget:

1. Bi-Cayley graphs on 4N vertices (four orbits, degree 6). Simulated annealing over the connection
   sets, with cost = vertices not reached within 5 steps from the four base vertices. This gives
   order 4N, which beats the record 684 once N >= 172.
2. Haar graphs on 2N vertices (one orbit pair, degree 6). Same annealing with cost = vertices not
   reached within 5 steps from A(e) and B(e). This gives order 2N, which beats 684 once N >= 343.
   Heisenberg(7), of order 343, is tried first.

Every candidate is checked with lib.is_valid before it is returned. If nothing valid is found, the
valid order-660 Haar graph (checked at run time) or a trivial graph is returned.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
MIN_N = 172   # bi-Cayley: 4 * 172 = 688 > 684 (record)
MIN_HAAR_N = 343  # Haar: 2 * 343 = 686 > 684 (record)


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

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


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


# ------------------------------------------------------------------------- generic cost

def _cost_gen(nbr, n, sources):
    """Vertices not reached within DIAM steps from each source, summed over sources (0 means all good)."""
    total = 0
    for src in sources:
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


# ------------------------------------------------------------------------- bi-Cayley graph

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


def _search_bicayley(MT, inv, N, deadline, rng):
    """Anneal the four connection sets until cost 0; return a checked (n, edges) or None."""
    n = 4 * N
    while time.monotonic() < deadline:
        a = int(rng.choice([2, 3, 3, 4]))
        sizes = {(0, 0): a, (0, 1): DEG - a, (1, 0): DEG - a, (1, 1): a}
        keys = list(sizes)
        S = {k: rng.choice(N, size=sizes[k], replace=False).astype(np.int64) for k in keys}
        cur = _cost_gen(_nbr(MT, inv, N, S), n, (0, N, 2 * N, 3 * N))
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
            c = _cost_gen(_nbr(MT, inv, N, newS), n, (0, N, 2 * N, 3 * N))
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            nbr = _nbr(MT, inv, N, S)
            edges = [(u, int(v)) for u in range(2 * N) for v in nbr[u]]
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


def _candidates_bicayley():
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


# ------------------------------------------------------------------------------- Haar graph

def _haar_nbr(MT, inv, N, S):
    """Neighbour array (2N x DEG).  A(g) ~ B(g*s) for s in S, so A-vertex g is g, B-vertex g is N+g."""
    g = np.arange(N, dtype=np.int64)
    S = np.asarray(S, dtype=np.int64)
    nbr = np.empty((2 * N, DEG), dtype=np.int64)
    nbr[:N] = N + MT[np.ix_(g, S)]
    nbr[N:] = MT[np.ix_(g, inv[S])]
    return nbr


def _search_haar(MT, inv, N, deadline, rng):
    """Anneal a single connection set S of size DEG until the Haar graph has diameter <= DIAM; return checked (n, edges) or None."""
    n = 2 * N
    while time.monotonic() < deadline:
        S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
        cur = _cost_gen(_haar_nbr(MT, inv, N, S), n, (0, N))
        stall = 0
        T = 0.6
        while time.monotonic() < deadline and cur > 0 and stall < 4000:
            pos = int(rng.integers(DEG))
            x = int(rng.integers(N))
            if x in S:
                stall += 1
                continue
            newS = S.copy()
            newS[pos] = x
            c = _cost_gen(_haar_nbr(MT, inv, N, newS), n, (0, N))
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            nbr = _haar_nbr(MT, inv, N, S)
            edges = [(u, int(v)) for u in range(N) for v in nbr[u]]
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


def _candidates_haar():
    """Heis(7) (order 343), then metacyclic groups of order 343..360, smallest first."""
    out = [("heis", 7, 0, 0)]
    for NN in range(MIN_HAAR_N, 361):
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            found = False
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and pow(lam, 1, m) != 1:
                    out.append(("meta", m, k, lam))
                    found = True
                    break
            if found:
                break
    return out


def _make(c):
    if c[0] == "meta":
        return group_meta(c[1], c[2], c[3])
    if c[0] == "heis":
        return _finish(group_heis(c[1]).__class__ and group_heis(c[1])[0]) if False else group_heis(c[1])
    return group_times_cyclic(group_heis(c[1]), c[2])


# --------------------------------------------------------------------------------------------- build

def _run_phase(cands, search, deadline, rng, make_fn):
    """Try candidate groups in turn, splitting the remaining time; return the largest valid graph found."""
    best = None
    for idx, c in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = make_fn(c)
            N = MT.shape[0]
            g = search(MT, inv, N, end, rng)
        except Exception:
            continue
        if g is not None and (best is None or g[0] > best[0]):
            best = g
            if best[0] > 684:
                break
    return best


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.85 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    # Phase 1: bi-Cayley graphs (order 4N), first 40% of the budget.
    phase1_end = t0 + 0.4 * budget
    best = _run_phase(_candidates_bicayley(),
                      lambda MT, inv, N, end, r: _search_bicayley(MT, inv, N, end, r),
                      phase1_end, rng, _make)

    # Phase 2: Haar graphs (order 2N, N >= 343 beats 684), remaining budget.
    if best is None or best[0] <= 684:
        h = _run_phase(_candidates_haar(),
                       lambda MT, inv, N, end, r: _search_haar(MT, inv, N, end, r),
                       deadline, rng, _make)
        if h is not None and (best is None or h[0] > best[0]):
            best = h

    if best is not None:
        return best
    return _fallback(d, D)
