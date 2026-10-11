import math
import random
import time

import lib


def _fallback(d, D):
    """Safe, verified-by-construction graphs used whenever the search fails."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------ groups

def _group_list(N, rng):
    """Candidate groups of order N: cyclic, plus some semidirect Z_m x| Z_k."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:4]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


# ------------------------------------------------ bi-Cayley k-base lifts
#
# NEW IDEA (not in the parent): a bi-Cayley graph with k base vertices per side.
# A-vertices are (A_i, x), B-vertices are (B_j, y), x, y in G. Block (i, j) with
# set S_ij gives edges (A_i, x) ~ (B_j, x*s) for s in S_ij. Each A_i and B_j has
# degree d when the row and column block sums are d. Left translations are
# automorphisms, so diameter <= 3 only needs to be checked from the 2k orbit
# representatives (A_i, e) and (B_j, e). The number of uncovered (rep, vertex)
# pairs is a cheap objective. It is computed with Python big-int bitmasks, and
# simulated annealing drives it to zero. For k = 2 the search has a larger
# design space than the difference-cover search, which only uses k = 1.

class _Bi:
    """Annealing state for a bi-Cayley graph with k base vertices per side."""

    def __init__(self, N, k, perms, sizes, rng):
        self.N = N
        self.k = k
        self.perms = perms
        self.rng = rng
        self.blocks = []  # [i, j, S] with S a list of distinct group elements
        for (i, j), s in sizes.items():
            if s > 0:
                self.blocks.append([i, j, rng.sample(range(N), s)])
        self.bad = self._bad()

    def _adj(self):
        N, k = self.N, self.k
        adj = [[] for _ in range(2 * k * N)]
        for i, j, S in self.blocks:
            off = (k + j) * N
            for g in S:
                p = self.perms[g]
                for x in range(N):
                    a = i * N + x
                    b = off + p[x]
                    adj[a].append(b)
                    adj[b].append(a)
        return adj

    def _bad(self):
        """Number of (orbit representative, vertex) pairs at distance > 3."""
        N, k = self.N, self.k
        n = 2 * k * N
        adj = self._adj()
        bit = [1 << v for v in range(n)]
        cl = [0] * n  # closed neighbourhoods
        for v in range(n):
            m = bit[v]
            for u in adj[v]:
                m |= bit[u]
            cl[v] = m
        r2 = [0] * n  # balls of radius 2
        for v in range(n):
            m = cl[v]
            for u in adj[v]:
                m |= cl[u]
            r2[v] = m
        reps = [i * N for i in range(k)] + [(k + j) * N for j in range(k)]
        bad = 0
        for r in reps:
            m = r2[r]
            for u in adj[r]:
                m |= r2[u]
            bad += n - bin(m).count("1")
        return bad

    def edges(self):
        N, k = self.N, self.k
        out = []
        for i, j, S in self.blocks:
            off = (k + j) * N
            for g in S:
                p = self.perms[g]
                for x in range(N):
                    out.append((i * N + x, off + p[x]))
        return 2 * k * N, out

    def run(self, steps, deadline, T):
        """Advance annealing by up to `steps` moves; return True once bad == 0."""
        rng, N = self.rng, self.N
        for s in range(steps):
            if self.bad == 0:
                return True
            if (s & 15) == 0 and time.monotonic() > deadline:
                return False
            blk = self.blocks[rng.randrange(len(self.blocks))]
            S = blk[2]
            idx = rng.randrange(len(S))
            old = S[idx]
            while True:
                x = rng.randrange(N)
                if x not in S:
                    break
            S[idx] = x
            new = self._bad()
            delta = new - self.bad
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                self.bad = new
            else:
                S[idx] = old
        return self.bad == 0


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    moore = lib.moore_bound(d, 3)
    best_n = base_n
    best = None

    cands = []
    for k in (1, 2):
        Nmax = moore // (2 * k)
        lo = best_n // (2 * k) + 1
        for N in range(max(lo, d + 1), Nmax + 1):
            for _o, mul, _inv in _group_list(N, rng):
                if k == 1:
                    opts = [d]
                else:
                    opts = sorted({d // 2, (d + 1) // 2})
                for a in opts:
                    cands.append((2 * k * N, rng.random(), k, N, a, mul))
    cands.sort(key=lambda c: (c[0], c[1]))
    cands = cands[:30]

    jobs = [{"n": n, "k": k, "N": N, "a": a, "mul": mul, "st": None}
            for n, _r, k, N, a, mul in cands]

    CHUNK = 300
    T = 0.6

    while time.monotonic() < deadline:
        active = [j for j in jobs if j["n"] > best_n]
        if not active:
            break
        for job in active:
            if time.monotonic() >= deadline:
                break
            if job["n"] <= best_n:
                continue
            k, N, a, mul = job["k"], job["N"], job["a"], job["mul"]
            if job["st"] is None:
                perms = [[mul(x, g) for x in range(N)] for g in range(N)]
                if k == 1:
                    sizes = {(0, 0): d}
                else:
                    sizes = {(0, 0): a, (0, 1): d - a, (1, 0): d - a, (1, 1): a}
                job["st"] = _Bi(N, k, perms, sizes, rng)
            st = job["st"]
            if st.run(CHUNK, deadline, T):
                n, edges = st.edges()
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best_n = n
                    best = (n, edges)

    if best is not None:
        return best
    return base_n, base_e
