"""Haar-graph annealing over non-abelian groups of order just above 342, with a two-orbit lift phase.

NEW IDEA (Haar annealing with a two-source cost).  A Haar graph on a group G with connection set S
(|S| = d) has vertices g (side A) and N+g (side B), with edges g ~ N + s*g for s in S.  Right
multiplication by h is an automorphism that is transitive on each side.  So diameter <= 5 holds iff the
radius-5 balls around the two identity vertices (0 on side A and N on side B) cover all 2N vertices.
The cost is the total uncovered count over those two balls, computed by a short numpy BFS.

Moves: replace one element of S with a random element, or with a product s_i * s_j of two current
elements (this keeps the new element inside the words already in use).  Metropolis acceptance, with
restarts once the search stalls.

Group candidates are the order 343 Heisenberg group mod 7, metacyclic groups of order 344..380, and
Heis(3) x Z_13 (351).  Any group of order N gives a Haar graph on 2N vertices, which beats 684 when N >= 343.

The two-orbit lift phase from the parent is kept for the remaining time.  Every result is checked with
lib.is_valid before it is returned, and the fallback is the 660-vertex Haar graph.
"""
import math
import time
from math import gcd

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
    return _finish(MT)


def heis(p):
    """Heisenberg group mod p (order p^3), element (a, b, c) -> a*p*p + b*p + c, identity 0.
    Product: (a, b, c)(a', b', c') = (a+a', b+b', c+c'+a*b')."""
    e = np.arange(p ** 3, dtype=np.int64)
    A, B, C = e // (p * p), (e // p) % p, e % p
    Ap = (A[:, None] + A[None, :]) % p
    Bp = (B[:, None] + B[None, :]) % p
    Cp = (C[:, None] + C[None, :] + A[:, None] * B[None, :]) % p
    return _finish(Ap * p * p + Bp * p + Cp)


def group_times_cyclic(grp, k):
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    C = (np.arange(k)[:, None] + np.arange(k)[None, :]) % k
    MT4 = MT0[:, None, :, None] * k + C[None, :, None, :]
    return _finish(MT4.reshape(n0 * k, n0 * k))


# ------------------------------------------------------------------------ Haar annealing (NEW)

def haar_cost(MT, S, invS, N):
    """Uncovered vertices over the radius-5 balls of the two identity vertices (0 on side A, N on side B).
    Haar graph: A-vertex g ~ B-vertex N + s*g for s in S.  0 means diameter <= 5."""
    total = 0
    for src in (0, N):
        vis = np.zeros(2 * N, dtype=bool)
        vis[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(5):
            fa = front[front < N]
            fb = front[front >= N] - N
            parts = []
            if fa.size:
                parts.append(N + MT[S[:, None], fa[None, :]].ravel())
            if fb.size:
                parts.append(MT[invS[:, None], fb[None, :]].ravel())
            if not parts:
                break
            nb = np.concatenate(parts)
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            vis[nb] = True
            front = nb
        total += 2 * N - int(vis.sum())
    return total


def haar_anneal(MT, inv, N, d, deadline, rng, T=1.0, patience=2500):
    """Anneal S (|S| = d) until haar_cost is 0 or the deadline passes.  Returns S or None."""
    while time.monotonic() < deadline:
        S = rng.choice(N, d, replace=False).astype(np.int64)
        invS = inv[S].copy()
        cur = haar_cost(MT, S, invS, N)
        since = 0
        while since < patience and time.monotonic() < deadline:
            if cur == 0:
                return S
            k = int(rng.integers(d))
            if rng.random() < 0.3:
                i, j = rng.integers(d, size=2)
                x = int(MT[S[int(i)], S[int(j)]])     # product move
            else:
                x = int(rng.integers(N))
            if x in S:
                since += 1
                continue
            old = int(S[k])
            S[k] = x
            invS[k] = inv[x]
            c2 = haar_cost(MT, S, invS, N)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
                since = 0 if delta < 0 else since + 1
            else:
                S[k] = old
                invS[k] = inv[old]
                since += 1
        if cur == 0:
            return S
    return None


def haar_edges(MT, N, S):
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in S:
        u = ar
        v = N + MT[int(s), ar]
        edges.extend(zip(u.tolist(), v.tolist()))
    return edges


def haar_candidates():
    """Groups of order 343 and up: Heis(7), metacyclic Z_m x| Z_k, and Heis(3) x Z_k.  Sorted by order."""
    out = [(343, lambda: heis(7))]
    for n in range(344, 381):
        for k in range(2, n):
            if n % k:
                continue
            m = n // k
            if m < 3:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((n, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
                    break
    out.append((351, lambda: group_times_cyclic(heis(3), 13)))
    out.append((378, lambda: group_times_cyclic(heis(3), 14)))
    out.sort(key=lambda t: t[0])
    return out[:12]


# ------------------------------------------------------------------------ two-orbit lift (parent)

PATTERNS = [
    [[3, 3], [3, 3]],
    [[2, 4], [4, 2]],
    [[4, 2], [2, 4]],
    [[1, 5], [5, 1]],
    [[5, 1], [1, 5]],
]


def build_nbr(MT, inv, M, volt):
    """Neighbour table (4M x 6).  Dart (i, j, g): A-vertex i*M+x gets neighbour (2+j)*M + x*g;
    B-vertex (2+j)*M+y gets neighbour i*M + y*g^-1."""
    N = 4 * M
    nbr = np.empty((N, 6), dtype=np.int64)
    ar = np.arange(M, dtype=np.int64)
    ca = [0, 0]
    cb = [0, 0]
    for (i, j), vs in volt.items():
        for g in vs:
            nbr[i * M + ar, ca[i]] = (2 + j) * M + MT[ar, g]
            ca[i] += 1
            nbr[(2 + j) * M + ar, cb[j]] = i * M + MT[ar, inv[g]]
            cb[j] += 1
    return nbr


def cost(nbr, N, M):
    """Uncovered vertices summed over the four orbit representatives, radius 5.  0 means diameter <= 5."""
    total = 0
    for s in (0, M, 2 * M, 3 * M):
        vis = np.zeros(N, dtype=bool)
        vis[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(5):
            nb = nbr[front].ravel()
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            vis[nb] = True
            front = nb
        total += N - int(vis.sum())
    return total


def to_edges(MT, M, volt):
    ar = np.arange(M, dtype=np.int64)
    E = []
    for (i, j), vs in volt.items():
        for g in vs:
            u = i * M + ar
            v = (2 + j) * M + MT[ar, g]
            E.extend(zip(u.tolist(), v.tolist()))
    return 4 * M, [(int(a), int(b)) for a, b in E]


def search_group(MT, inv, M, deadline, rng, T=2.0, patience=4000):
    """Annealing over voltages with random restarts.  Returns a volt dict with cost 0, or None."""
    N = 4 * M
    while time.monotonic() < deadline:
        pat = PATTERNS[int(rng.integers(len(PATTERNS)))]
        volt = {}
        for i in range(2):
            for j in range(2):
                c = pat[i][j]
                volt[(i, j)] = [int(x) for x in rng.choice(M, c, replace=False)] if c > 0 else []
        cur = cost(build_nbr(MT, inv, M, volt), N, M)
        pairs = [p for p in volt if volt[p]]
        since = 0
        while since < patience and time.monotonic() < deadline:
            if cur == 0:
                return volt
            p = pairs[int(rng.integers(len(pairs)))]
            k = int(rng.integers(len(volt[p])))
            x = int(rng.integers(M))
            if x in volt[p]:
                since += 1
                continue
            old = volt[p][k]
            volt[p][k] = x
            c2 = cost(build_nbr(MT, inv, M, volt), N, M)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
                since = 0 if delta < 0 else since + 1
            else:
                volt[p][k] = old
                since += 1
        if cur == 0:
            return volt
    return None


def candidates():
    """Groups of order 166..200 (metacyclic, non-abelian) plus Heis(3) x Z_7 (189), sorted by order."""
    out = []
    for m in range(3, 201):
        for k in range(2, 200 // m + 1):
            n_ = m * k
            if n_ < 166 or n_ > 200:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((n_, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
                    break
    out.append((189, lambda: group_times_cyclic(heis(3), 7)))
    out.sort(key=lambda t: t[0])
    return out[:10]


# ------------------------------------------------------------------------ fallback

FALLBACK_S = [0, 179, 116, 180, 47, 306]


def haar_fallback():
    """Valid 660-vertex Haar graph (group_meta(33, 10, 26))."""
    MT, _ = group_meta(33, 10, 26)
    N = MT.shape[0]
    edges = []
    for s in FALLBACK_S:
        for g in range(N):
            edges.append((g, N + int(MT[s, g])))
    return 2 * N, edges


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


# ------------------------------------------------------------------------ entry point

TARGET = (6, 5)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(1.0, min(0.80 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    best = None

    # Phase 1: Haar annealing over groups of order >= 343 (Haar graph has 2N vertices).
    haar_deadline = t0 + 0.65 * budget
    hc = haar_candidates()
    for idx, (n_, builder) in enumerate(hc):
        now = time.monotonic()
        rem = haar_deadline - now
        if rem <= 0.3:
            break
        end = now + rem / (len(hc) - idx)
        try:
            MT, inv = builder()
            N = MT.shape[0]
            S = haar_anneal(MT, inv, N, d, end, rng)
            if S is None:
                continue
            edges = haar_edges(MT, N, S)
            n = 2 * N
            if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                best = (n, edges)
        except Exception:
            continue

    # Phase 2: two-orbit lifts for the remaining time (skips candidates that cannot beat best).
    cands = candidates()
    for idx, (n_, builder) in enumerate(cands):
        if best is not None and 4 * n_ <= best[0]:
            continue
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.5:
            break
        end = now + rem / (len(cands) - idx)
        try:
            MT, inv = builder()
            M = MT.shape[0]
            volt = search_group(MT, inv, M, end, rng)
            if volt is None:
                continue
            n, edges = to_edges(MT, M, volt)
            if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                best = (n, edges)
        except Exception:
            continue

    if best is not None:
        return best
    try:
        n, edges = haar_fallback()
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
