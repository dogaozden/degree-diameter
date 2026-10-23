"""Combined two-orbit search for the bipartite degree-diameter problem, d=6, D=5 (numpy + lib only).

Two families, each candidate verified with lib.is_valid before it is accepted:
  1. Bi-Cayley graphs on four orbits (A0, A1, B0, B1) of a group G with |G| = N, giving 4N vertices.
     Connection sets S_ij have sizes a, 6-a, 6-a, a (a in {2,3,4}). Anneal the sets so that the
     radius-5 balls of the four orbit representatives cover everything. N >= 166 beats the 660 fallback.
  2. Haar graphs on 2M vertices: A(g) ~ B(g*s) for s in S, |S| = 6. Sources A(e) and B(e) suffice.
     M >= 343 beats the record 684.
Fallback: a checked 660-vertex Haar graph, then a trivial valid graph.
"""
import itertools
import math
import time
from math import gcd

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l)."""
    if gcd(lam, m) != 1 or pow(lam, k, m) != 1 % m:
        raise ValueError("bad metacyclic parameters")
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Table of a group given by (N, c) integer coordinates (identity first) and a vectorised product."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sorted_codes = codes[order]
    MT = np.empty((N, N), dtype=np.int64)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sorted_codes, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_heis(p=3):
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p,
                         (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)

    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT0, inv0) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    C = (np.arange(k)[:, None] + np.arange(k)[None, :]) % k
    MT4 = MT0[:, None, :, None] * k + C[None, :, None, :]
    return _finish(MT4.reshape(n0 * k, n0 * k))


# ------------------------------------------------------------------------------ cost helpers

def _uncovered(nbr, sources):
    """Total vertices not reached within DIAM steps from each source (0 means all sources are good)."""
    n = nbr.shape[0]
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


# ----------------------------------------------------------------------- bi-Cayley (4 orbits)

def _bi_nbr(MT, inv, N, S):
    """Neighbour table (4N x DEG). Orbits: A0 = 0..N-1, A1 = N..2N-1, B0 = 2N..3N-1, B1 = 3N..4N-1.
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


def _bi_search(MT, inv, N, deadline, rng):
    """Anneal the four connection sets until cost 0; return a checked (n, edges) or None."""
    sources = [0, N, 2 * N, 3 * N]
    while time.monotonic() < deadline:
        a = int(rng.choice([2, 3, 3, 4]))
        sizes = {(0, 0): a, (0, 1): DEG - a, (1, 0): DEG - a, (1, 1): a}
        keys = list(sizes)
        S = {k: rng.choice(N, size=sizes[k], replace=False).astype(np.int64) for k in keys}
        cur = _uncovered(_bi_nbr(MT, inv, N, S), sources)
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
            c = _uncovered(_bi_nbr(MT, inv, N, newS), sources)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            nbr = _bi_nbr(MT, inv, N, S)
            n = 4 * N
            edges = [(u, int(v)) for u in range(2 * N) for v in nbr[u]]
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


# ------------------------------------------------------------------------------ Haar graphs

def _haar_nbr(MT, inv, M, S):
    """Neighbour table (2M x DEG): A(g) ~ B(g*s) for s in S; B(h) ~ A(h*s^-1)."""
    g = np.arange(M, dtype=np.int64)
    nbr = np.empty((2 * M, DEG), dtype=np.int64)
    for c, s in enumerate(S):
        nbr[:M, c] = M + MT[g, s]
        nbr[M:, c] = MT[g, inv[s]]
    return nbr


def _haar_search(MT, inv, M, deadline, rng):
    """Anneal a 6-element connection set until the sources A(e), B(e) cover everything within 5."""
    sources = [0, M]
    while time.monotonic() < deadline:
        S = [int(x) for x in rng.choice(M, DEG, replace=False)]
        cur = _uncovered(_haar_nbr(MT, inv, M, S), sources)
        stall = 0
        T = 0.6
        while time.monotonic() < deadline and cur > 0 and stall < 3000:
            pos = int(rng.integers(DEG))
            x = int(rng.integers(M))
            if x in S:
                stall += 1
                continue
            new = list(S)
            new[pos] = x
            c = _uncovered(_haar_nbr(MT, inv, M, new), sources)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = new, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            n = 2 * M
            edges = [(g, M + int(MT[g, s])) for s in S for g in range(M)]
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


# ------------------------------------------------------------------------------ candidates

def _meta_specs(lo, hi, per=2):
    """Non-abelian metacyclic groups Z_m x| Z_k with order in [lo, hi], sorted by order."""
    out = []
    for M in range(lo, hi + 1):
        for k in range(2, M):
            if M % k:
                continue
            m = M // k
            if m < 3:
                continue
            cnt = 0
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append(("meta", m, k, lam))
                    cnt += 1
                    if cnt >= per:
                        break
    return out


def _order(spec):
    return spec[1] * spec[2] if spec[0] == "meta" else 27 * spec[1]


def _make(spec):
    if spec[0] == "meta":
        return group_meta(spec[1], spec[2], spec[3])
    return group_times_cyclic(group_heis(3), spec[1])


def _bi_specs():
    specs = _meta_specs(166, 200)[:10]
    specs.append(("heis", 7))  # Heis(3) x Z_7, order 189
    return sorted(specs, key=_order)


def _haar_specs():
    specs = _meta_specs(343, 370)[:8]
    specs += [("heis", 13), ("heis", 14)]  # orders 351 and 378
    return sorted(specs, key=_order)


# ----------------------------------------------------------------------------------- runner

def _run(specs, mult, search, deadline, rng, best):
    """Try candidates in order, sharing the remaining time; keep the largest valid graph."""
    for idx, spec in enumerate(specs):
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.2:
            break
        if best is not None and mult * _order(spec) <= best[0]:
            continue
        end = now + rem / (len(specs) - idx)
        try:
            MT, inv = _make(spec)
            N = MT.shape[0]
            res = search(MT, inv, N, end, rng)
        except Exception:
            continue
        if res is not None and (best is None or res[0] > best[0]):
            best = res
    return best


# ------------------------------------------------------------------------------- fallbacks

def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    try:
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
            n, e = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, e, d, D):
                return n, e
        n, e = lib.haar_graph(d, range(d))
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return 2, [(0, 1)]


def _fallback660(d, D):
    """Checked order-660 Haar graph for d=6, D=5, else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        N = MT.shape[0]
        S = [0, 179, 116, 180, 47, 306]
        edges = [(g, N + int(MT[s, g])) for s in S for g in range(N)]
        if lib.is_valid(2 * N, edges, d, D):
            return 2 * N, edges
    except Exception:
        pass
    return trivial(d, D)


# ----------------------------------------------------------------------------------- entry

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    best = _run(_bi_specs(), 4, _bi_search, t0 + 0.55 * budget, rng, best)
    best = _run(_haar_specs(), 2, _haar_search, deadline, rng, best)

    if best is not None:
        return best
    return _fallback660(d, D)
