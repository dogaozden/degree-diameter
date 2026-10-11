import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over small groups.
#
# Group G of order M, connection set S of d distinct elements.
# Vertices A_g = g and B_h = M + h; A_g ~ B_{g*s} for s in S.
# Left multiplication is an automorphism, so the graph is vertex-transitive
# on each side. Diameter <= D reduces to checking BFS from A_e and B_e only.
# This is a different family from the parent's voltage lifts: a single
# orbit, with no base-graph structure, searched directly over group elements.
# ----------------------------------------------------------------------------

class _Group:
    def __init__(self, m, k, r):
        order, mul, inv = lib.semidirect_group(m, k, r)
        self.M = order
        self._mul = mul
        self.inv_list = [inv(s) for s in range(order)]
        self._cache = {}

    def R(self, s):
        """Right-multiplication table g -> g*s as a numpy array (cached)."""
        arr = self._cache.get(s)
        if arr is None:
            mul = self._mul
            arr = np.array([mul(g, s) for g in range(self.M)], dtype=np.int64)
            self._cache[s] = arr
        return arr

    def cost(self, S, D):
        """Number of (source, vertex) pairs at distance > D from A_e and B_e. Zero iff valid."""
        M = self.M
        N = 2 * M
        adj = np.empty((N, len(S)), dtype=np.int64)
        for j, s in enumerate(S):
            adj[:M, j] = M + self.R(s)
            adj[M:, j] = self.R(self.inv_list[s])
        total = 0
        for src in (0, M):
            seen = np.zeros(N, dtype=bool)
            seen[src] = True
            frontier = np.array([src], dtype=np.int64)
            for _ in range(D):
                nb = adj[frontier].ravel()
                nb = nb[~seen[nb]]
                if nb.size == 0:
                    break
                nb = np.unique(nb)
                seen[nb] = True
                frontier = nb
            total += N - int(seen.sum())
        return total

    def edges(self, S):
        M = self.M
        E = []
        for s in S:
            Rl = self.R(s).tolist()
            E.extend((g, M + Rl[g]) for g in range(M))
        return 2 * M, E


def _groups_of_order(M, rng, per_k=4):
    """Candidate semidirect products Z_m x| Z_k of order M (r=1 gives direct products)."""
    out = []
    for k in range(1, M + 1):
        if M % k:
            continue
        m = M // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        rng.shuffle(rs)
        for r in rs[:per_k]:
            out.append((m, k, r))
    return out


def _search_group(G, d, D, rng, deadline):
    """Hill-climb a connection set S (|S| = d) in G until the bi-Cayley graph has diameter <= D."""
    M = G.M
    if M < d:
        return None
    if M == d:
        S = list(range(M))
        return S if G.cost(S, D) == 0 else None
    while time.monotonic() < deadline:
        S = rng.sample(range(M), d)
        c = G.cost(S, D)
        stall = 0
        while c > 0 and stall < 300 and time.monotonic() < deadline:
            i = rng.randrange(d)
            x = rng.randrange(M)
            if x in S:
                continue
            T = S[:]
            T[i] = x
            ct = G.cost(T, D)
            if ct < c:
                stall = 0
            else:
                stall += 1
            if ct <= c or rng.random() < 0.02:
                S, c = T, ct
        if c == 0:
            return S
    return None


def _try_order(M, d, D, rng, deadline):
    """Try up to 4 random groups of order M within the deadline. Returns (group, S) or None."""
    groups = _groups_of_order(M, rng)
    if not groups:
        return None
    rng.shuffle(groups)
    groups = groups[:4]
    for spec in groups:
        now = time.monotonic()
        if now >= deadline:
            break
        per = (deadline - now) / max(1, len(groups))
        G = _Group(*spec)
        S = _search_group(G, d, D, rng, min(deadline, time.monotonic() + per))
        if S is not None:
            return G, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.3, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
            return True
        return False

    # Projective plane incidence graph (diameter 3), valid for D >= 3.
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break

    # Bi-Cayley search: sliding window over group orders M, least-tried first.
    Mmax = lib._moore_bound(d, D) // 2
    if Mmax >= d and time.monotonic() < deadline:
        lo_w = max(d, (Mmax * 2) // 5)
        W = 16
        attempts = {}
        best_M = 0
        while time.monotonic() < deadline and lo_w <= Mmax:
            lo_w = max(lo_w, best_M + 1)
            hi_w = min(Mmax, lo_w + W - 1)
            if lo_w > hi_w:
                break
            window = list(range(lo_w, hi_w + 1))
            if min(attempts.get(x, 0) for x in window) >= 3:
                lo_w += 4
                continue
            M = min(window, key=lambda x: (attempts.get(x, 0), rng.random()))
            a = attempts.get(M, 0)
            attempts[M] = a + 1
            budget_M = min(6.0, 0.4 * (1 + a))
            res = _try_order(M, d, D, rng, min(deadline, time.monotonic() + budget_M))
            if res is not None:
                G, S = res
                n, e = G.edges(S)
                if consider(n, e):
                    best_M = max(best_M, M)

    # Final guard: the stored graph is always valid (fallback is K_{d,d}).
    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, [(int(u), int(v)) for u, v in best_e]
