import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families for D = 3: projective plane incidence and Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Haar graphs over arbitrary finite groups (a different family from the
# earlier voltage lifts).
#
# Vertices: A_x = x (0 <= x < G) and B_y = G + y.
# Edges:    A_x -- B_{x*s} for every s in S, where |S| = d.
#
# Left multiplication by t is an automorphism that moves A_0 to A_t and B_0
# to B_t, so the diameter is <= D iff both A_0 and B_0 reach everything
# within distance D. Only two BFS runs are needed per candidate.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul, inv) for a random group of order G: semidirect Z_m x| Z_k or cyclic."""
    ks = [k for k in range(2, 13) if G % k == 0 and G // k >= 3]
    if ks and rng.random() < 0.7:
        k = rng.choice(ks)
        m = G // k
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            r = rng.choice(rs)
            return lib.semidirect_group(m, k, r)
    return lib.cyclic_group(G)


class _Haar:
    """Cost oracle for Haar graphs over a fixed group of order G."""

    def __init__(self, G, mul, inv, D):
        self.G = G
        self.mul = mul
        self.inv = inv
        self.D = D
        self.cache = {}

    def perm(self, g):
        """Permutation x -> x*g, cached per group element."""
        p = self.cache.get(g)
        if p is None:
            mul = self.mul
            p = [mul(x, g) for x in range(self.G)]
            self.cache[g] = p
        return p

    def cost(self, S, limit=float("inf")):
        """Total number of vertices not reached within D from A_0 and from B_0.

        Zero exactly when the Haar graph has diameter <= D. Returns early with a
        value above `limit` once the running total exceeds it.
        """
        G = self.G
        D = self.D
        fwd = [self.perm(s) for s in S]
        bwd = [self.perm(self.inv(s)) for s in S]
        total = 0
        for start_side in (0, 1):
            seen_a = [False] * G
            seen_b = [False] * G
            if start_side == 0:
                seen_a[0] = True
            else:
                seen_b[0] = True
            side = start_side
            frontier = [0]
            count = 1
            for _ in range(D):
                nxt = []
                if side == 0:
                    for x in frontier:
                        for p in fwd:
                            y = p[x]
                            if not seen_b[y]:
                                seen_b[y] = True
                                nxt.append(y)
                else:
                    for y in frontier:
                        for p in bwd:
                            x = p[y]
                            if not seen_a[x]:
                                seen_a[x] = True
                                nxt.append(x)
                count += len(nxt)
                frontier = nxt
                side ^= 1
                if not frontier:
                    break
            total += 2 * G - count
            if total > limit:
                return total
        return total

    def edges(self, S):
        """Edge list (n, edges) of the Haar graph for connection set S."""
        G = self.G
        E = []
        for s in S:
            p = self.perm(s)
            for x in range(G):
                E.append((x, G + p[x]))
        return 2 * G, E


def _anneal_haar(H, d, rng, until):
    """Simulated annealing over connection sets S (|S| = d, 0 in S). Returns S or None."""
    G = H.G
    S = [0] + rng.sample(range(1, G), d - 1)
    c = H.cost(S)
    best_c = c
    T = 2.0
    stale = 0
    while c > 0 and time.monotonic() < until:
        i = rng.randrange(1, d)
        new = rng.randrange(1, G)
        if new in S:
            continue
        T2 = S[:]
        T2[i] = new
        limit = c - T * math.log(1.0 - rng.random())
        c2 = H.cost(T2, limit)
        if c2 <= limit:
            S, c = T2, c2
        if c < best_c:
            best_c = c
            stale = 0
        else:
            stale += 1
        T = max(0.3, T * 0.999)
        if stale > 3000 and c > 0:
            S = [0] + rng.sample(range(1, G), d - 1)
            c = H.cost(S)
            best_c = c
            T = 2.0
            stale = 0
    return S if c == 0 else None


def _haar_phase(d, D, best_n, deadline, rng, consider):
    """Search for Haar graphs of growing group order G (vertices = 2G)."""
    gmax = lib.moore_bound(d, D) // 2
    last_ok = max(d, best_n // 2)
    G = max(d + 1, last_ok + 1, int(0.4 * gmax))
    step = max(1, G // 50)
    while time.monotonic() < deadline and G <= gmax:
        rem = deadline - time.monotonic()
        per_G = time.monotonic() + max(3.0, 0.25 * rem)
        found = None
        while found is None and time.monotonic() < per_G and time.monotonic() < deadline:
            order, mul, inv = _sample_group(G, rng)
            H = _Haar(order, mul, inv, D)
            until = min(per_G, deadline, time.monotonic() + 3.0)
            S = _anneal_haar(H, d, rng, until)
            if S is not None:
                found = H.edges(S)
        if found is not None:
            consider(found[0], found[1])
            last_ok = G
            G = G + step
        else:
            if step > 1:
                step = max(1, step // 2)
            G = last_ok + step


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # d = 2: cycle C_{2D} is Moore-optimal (Haar graph of Z_D with S = {0, 1}).
    if d == 2 and D >= 2:
        consider(*lib.haar_graph(D, [0, 1]))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Main search: Haar graphs over non-cyclic and cyclic groups.
    # Skipped when the current graph already meets the Moore bound.
    if D >= 3 and d >= 3 and best_n < lib.moore_bound(d, D):
        _haar_phase(d, D, best_n, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
