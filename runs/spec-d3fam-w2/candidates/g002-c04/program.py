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
        return lib.haar_graph(d, range(d))          # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)  # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)    # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------
# New construction: multi-orbit voltage lifts with annealed voltages.
#
# Base multigraph: k A-vertices and k B-vertices, each of degree d (random
# balanced bipartite multigraph with d darts per A-vertex and d per B-vertex).
# Every dart (i, j, g) over a finite group G of order N lifts to the edges
# a_{i,x} ~ b_{j, x*g}. The lift has 2kN vertices, is bipartite, and has max
# degree <= d. Left multiplication by G is an automorphism that acts regularly
# on each orbit, so the diameter test is a single 3-round bitset reachability
# computation. Voltages are annealed to minimise the number of vertex pairs at
# distance > 3. Unlike the single-orbit difference-cover search, k > 1 gives
# 2kN vertices with a much larger search space for the same order.
# ----------------------------------------------------------------------------

def _group_candidates(N, rng):
    """Cyclic group of order N plus a few semidirect products Z_m x| Z_k."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:2]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


class _OrbitSearch:
    """Annealing over voltages of a fixed random balanced base multigraph."""

    def __init__(self, k, d, N, M, rng):
        self.k, self.d, self.N, self.M, self.rng = k, d, N, M, rng
        self.n = 2 * k * N
        targets = [j for j in range(k) for _ in range(d)]
        rng.shuffle(targets)
        self.darts = []
        for i in range(k):
            for t in range(d):
                self.darts.append([i, targets[i * d + t], rng.randrange(N)])
        self.cost = self._cost()
        self.best_cost = self.cost

    def _adj(self):
        k, N, M, n = self.k, self.N, self.M, self.n
        adj = [set() for _ in range(n)]
        for i, j, g in self.darts:
            bbase = (k + j) * N
            for x in range(N):
                a = i * N + x
                b = bbase + M[x][g]
                adj[a].add(b)
                adj[b].add(a)
        return adj

    def _cost(self):
        adj = self._adj()
        n = self.n
        reach = [1 << v for v in range(n)]
        for _ in range(3):
            new = []
            for v in range(n):
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                new.append(r)
            reach = new
        return sum(n - r.bit_count() for r in reach) // 2

    def anneal(self, steps, T):
        rng = self.rng
        for _ in range(steps):
            if self.cost == 0:
                return
            idx = rng.randrange(len(self.darts))
            old = self.darts[idx][2]
            g = rng.randrange(self.N)
            if g == old:
                continue
            self.darts[idx][2] = g
            c = self._cost()
            if c <= self.cost or rng.random() < math.exp(-(c - self.cost) / T):
                self.cost = c
                if c < self.best_cost:
                    self.best_cost = c
            else:
                self.darts[idx][2] = old

    def graph(self):
        adj = self._adj()
        edges = sorted({(a, b) for a in range(self.n) for b in adj[a] if a < b})
        return self.n, edges


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

    moore = lib.moore_bound(d, D)
    best_n, best_e = base_n, base_e

    # Build jobs: (k, group order N) with 2kN strictly above the current best.
    jobs = []
    for k in (2, 3, 4, 1):
        n_min = base_n + 1
        N_min = max(2, -(-n_min // (2 * k)))
        N_max = moore // (2 * k)
        for N in range(N_min, min(N_max, N_min + 3) + 1):
            for _order, mul, _inv in _group_candidates(N, rng)[:3]:
                M = [[mul(x, g) for g in range(N)] for x in range(N)]
                s = _OrbitSearch(k, d, N, M, rng)
                jobs.append({"n": 2 * k * N, "s": s})
            if len(jobs) >= 60:
                break
    jobs.sort(key=lambda j: j["n"])

    active = list(jobs)
    while active and time.monotonic() < deadline:
        survivors = []
        for job in active:
            if time.monotonic() >= deadline:
                survivors.append(job)
                continue
            if job["n"] <= best_n:
                continue
            s = job["s"]
            s.anneal(40, 1.5)
            if s.cost == 0:
                n, edges = s.graph()
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best_n, best_e = n, edges
                continue
            survivors.append(job)
        active = [j for j in survivors if j["n"] > best_n]

    if best_n > base_n and lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return base_n, base_e
