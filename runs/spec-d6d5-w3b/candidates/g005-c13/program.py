import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy (new in this version):
#   * Safe baselines: K_{d,d}, and the PG(2,q) incidence graph for D >= 3.
#   * Main family: bi-Cayley graphs over a finite group G of order m.
#     Vertices are A_x and B_y for x, y in G. Connection set S (|S| = d) gives
#     A_x ~ B_{x*s} for s in S. Left multiplication is an automorphism that
#     fixes each side, so each side is one orbit. The diameter is therefore
#     decided by two BFS runs, one from A_e and one from B_e. The order is 2m.
#   * Groups: cyclic Z_m, and semidirect products Z_a x| Z_k. Ladder search
#     over m: keep the largest feasible order and try larger orders with
#     simulated annealing on S. Every output is checked by lib.is_valid.
# ----------------------------------------------------------------------------


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


class _Group:
    """Finite group with lazily cached right-multiplication permutations."""

    def __init__(self, order, mul, inv):
        self.G = order
        self.mul = mul
        self.inv = inv
        self._R = {}

    def R(self, t):
        """Permutation x -> x * t as a list (index 0 is the identity)."""
        r = self._R.get(t)
        if r is None:
            mul = self.mul
            r = [mul(x, t) for x in range(self.G)]
            self._R[t] = r
        return r


def _sample_group(G, rng):
    """Random group of order G: cyclic or Z_a x| Z_k2 with a * k2 = G."""
    divs = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    for _ in range(60):
        k2 = rng.choice(divs)
        a = G // k2
        if k2 == 1:
            order, mul, inv = lib.cyclic_group(a)
            return _Group(order, mul, inv)
        cands = [r for r in rng.sample(range(1, a), min(a - 1, 40))
                 if math.gcd(r, a) == 1 and pow(r, k2, a) == 1 % a]
        if cands:
            r = rng.choice(cands)
            order, mul, inv = lib.semidirect_group(a, k2, r)
            return _Group(order, mul, inv)
    return None


def _reach_bad(G, D, Rs, Ri):
    """Number of vertices not within distance D of A_e or of B_e (zero means valid).

    Rs[t] is the permutation x -> x*s for s in S; Ri[t] is x -> x*s^{-1}.
    A-vertex x has neighbours B_{x s}. B-vertex y has neighbours A_{y s^{-1}}.
    Vertex indices: A_x = x, B_y = G + y.
    """
    N = 2 * G
    bad = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for R in Rs:
                        v = G + R[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    y = u - G
                    for R in Ri:
                        v = R[y]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            if not nxt:
                break
            frontier = nxt
        bad += N - count
    return bad


def _anneal_set(grp, d, D, rng, deadline):
    """Anneal a connection set S of d distinct elements of grp so that the bi-Cayley graph has diameter <= D."""
    G = grp.G
    if d > G:
        return None
    S = rng.sample(range(G), d)
    Rs = [grp.R(s) for s in S]
    Ri = [grp.R(grp.inv(s)) for s in S]
    c = _reach_bad(G, D, Rs, Ri)
    T = 2.0
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        t = rng.randrange(G)
        if t in S:
            continue
        old = S[i]
        old_R, old_Ri = Rs[i], Ri[i]
        S[i] = t
        Rs[i] = grp.R(t)
        Ri[i] = grp.R(grp.inv(t))
        c2 = _reach_bad(G, D, Rs, Ri)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[i] = old
            Rs[i] = old_R
            Ri[i] = old_Ri
        T = max(0.1, T * 0.995)
    return list(S) if c == 0 else None


def _edges_from(grp, S):
    """Edge list of the bi-Cayley graph with connection set S over grp (2G vertices)."""
    G = grp.G
    E = []
    for s in S:
        R = grp.R(s)
        for x in range(G):
            E.append((x, G + R[x]))
    return 2 * G, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 5.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Ladder search over bi-Cayley orders G (total order 2G).
    cur = best_n // 2
    fails = 0
    hi_cap = moore // 2
    while time.monotonic() < deadline:
        if cur + 1 > hi_cap:
            break
        step = max(2, cur // 25) + fails // 8
        G = rng.randint(cur + 1, min(hi_cap, cur + step))
        grp = _sample_group(G, rng)
        if grp is None:
            fails += 1
            continue
        att_end = min(deadline, time.monotonic() + 1.5)
        S = _anneal_set(grp, d, D, rng, att_end)
        if S is None:
            fails += 1
            continue
        n, E = _edges_from(grp, S)
        if consider(n, E):
            cur = G
            fails = 0
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
