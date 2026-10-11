import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline families (projective plane and Araujo-Pardo-Lopez). These give the
# safe fallback for the D = 3 calibration case and a floor for the others.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over semidirect products Z_m x| Z_k, found by annealing.
#
# Vertices: A_g and B_h for g, h in a group G of order N.
# Edges: A_g -- B_{g*s} for each s in a set S of d distinct group elements.
# Left multiplication by any element is an automorphism, so the graph is
# vertex-transitive on each side. Diameter <= D therefore holds iff every
# vertex is within distance D of A_e and of B_e. The cost is the number of
# unreached vertices from those two sources, computed with numpy BFS over
# group indices. Zero cost means a valid graph with 2N vertices, max degree d.
# ----------------------------------------------------------------------------

def _group_options(N):
    """Candidate (m, k, r) with Z_m x|_r Z_k of order N, k up to 12."""
    opts = []
    for k in range(1, 13):
        if N % k or N // k < 2:
            continue
        m = N // k
        if k == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


class _Group:
    """Group of order G with lazily cached right-multiplication tables g -> g*s."""

    def __init__(self, order, mul, inv):
        self.G = order
        self.mul = mul
        self.inv = inv
        self._R = {}

    def R(self, s):
        arr = self._R.get(s)
        if arr is None:
            mul = self.mul
            arr = np.array([mul(g, s) for g in range(self.G)], dtype=np.int64)
            self._R[s] = arr
        return arr


def _unreached(grp, S, D):
    """Number of (source, vertex) pairs at distance > D, sources A_e and B_e. Zero means valid."""
    G = grp.G
    Rs = [grp.R(s) for s in S]
    Ri = [grp.R(grp.inv(s)) for s in S]
    total = 0
    for start in (0, 1):
        seen = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        seen[start][0] = True          # identity has index 0
        idx = np.array([0], dtype=np.int64)
        side = start
        for _ in range(D):
            # From side 0 (A_g) go to B_{g s}; from side 1 (B_h) go to A_{h s^-1}.
            tabs = Rs if side == 0 else Ri
            cand = np.unique(np.concatenate([t[idx] for t in tabs]))
            other = 1 - side
            cand = cand[~seen[other][cand]]
            if cand.size == 0:
                break
            seen[other][cand] = True
            idx = cand
            side = other
        total += 2 * G - int(seen[0].sum()) - int(seen[1].sum())
    return total


def _anneal_group(grp, d, D, rng, deadline):
    """Anneal a set S of d distinct group elements. Returns (S or None, cost)."""
    G = grp.G
    S = rng.sample(range(G), d)
    c = _unreached(grp, S, D)
    T = 2.0
    while c > 0 and time.monotonic() < deadline:
        T = max(0.05, T * 0.9995)
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        T2 = S[:]
        T2[i] = new
        c2 = _unreached(grp, T2, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = T2, c2
    return (S if c == 0 else None), c


def _lift_edges(grp, S):
    """Edges of the bi-Cayley graph: vertices A_g = g, B_h = G + h."""
    G = grp.G
    edges = []
    for s in S:
        R = grp.R(s)
        for g in range(G):
            edges.append((g, G + int(R[g])))
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 2 and time.monotonic() < deadline:
        moore = lib._moore_bound(d, D)
        G = max(best[0] // 2 + 1, int(0.2 * moore / 2), d + 1)
        fails = 0
        attempt_budget = max(3.0, 0.08 * time_limit)
        while time.monotonic() < deadline:
            if G < d + 1:
                G = d + 1
            opts = _group_options(G)
            if not opts:
                G += 1
                continue
            rng.shuffle(opts)
            found = None
            for (m, k, r) in opts[:3]:
                if time.monotonic() >= deadline:
                    break
                order, mul, inv = lib.semidirect_group(m, k, r)
                grp = _Group(order, mul, inv)
                att_dl = min(deadline, time.monotonic() + attempt_budget / 3)
                S, _c = _anneal_group(grp, d, D, rng, att_dl)
                if S is not None:
                    found = (grp, S)
                    break
            if found is not None:
                n, e = _lift_edges(found[0], found[1])
                consider(n, e)
                fails = 0
                G += max(1, G // 60)
            else:
                fails += 1
                if fails >= 2:
                    fails = 0
                    G -= max(1, G // 200)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
