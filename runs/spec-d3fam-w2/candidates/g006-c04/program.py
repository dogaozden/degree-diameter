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


# ------------------------------------------------------------ group helpers

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
        for r in rs[:6]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _mul_table(N, mul):
    """mt[x][g] = x * g, precomputed for fast lift construction."""
    return [[mul(x, g) for g in range(N)] for x in range(N)]


# ------------------------------------------------ multi-orbit voltage lifts
#
# NEW IDEA (not in the parent): a bipartite base multigraph with k vertices on
# each side (2k base vertices), every A-vertex having exactly d outgoing darts,
# and B-vertices receiving exactly d darts each. Its Z-lift over a group G of
# order N has 2kN vertices and is d-regular on the A side.
#
# The left action x -> h x is a graph automorphism of the lift, so the fibre
# over each base vertex is one orbit. The diameter-3 test therefore needs only
# 2k BFS sources, one per base vertex, instead of all vertices. The search
# minimises the number of unreached (source, vertex) pairs at distance > 3,
# plus duplicate-dart penalties, by annealing over voltages and head swaps.
# Parent's k=1 case is the special case of this family.

class _LiftSearch:
    """Annealing over voltages and dart heads for a k-by-k base multigraph over G."""

    def __init__(self, k, N, mt, d, rng):
        self.k, self.N, self.mt, self.d, self.rng = k, N, mt, d, rng
        self.m = k * d                       # total darts
        self.heads = [j for j in range(k) for _ in range(d)]
        rng.shuffle(self.heads)              # every B-vertex gets exactly d darts
        self.volt = [rng.randrange(N) for _ in range(self.m)]
        self.n = 2 * k * N
        self.cost = self._cost()

    def _sources(self):
        k, N = self.k, self.N
        return [i * N for i in range(k)] + [(k + j) * N for j in range(k)]

    def _cost(self):
        k, N, d, mt, n = self.k, self.N, self.d, self.mt, self.n
        adj = [[] for _ in range(n)]
        seen = set()
        dup = 0
        for t in range(self.m):
            i = t // d
            j = self.heads[t]
            g = self.volt[t]
            key = (i, j, g)
            if key in seen:
                dup += 1
            seen.add(key)
            ba = i * N
            bb = (k + j) * N
            for x in range(N):
                a = ba + x
                b = bb + mt[x][g]
                adj[a].append(b)
                adj[b].append(a)
        bad = 0
        for s in self._sources():
            visited = bytearray(n)
            visited[s] = 1
            frontier = [s]
            reached = 1
            for _ in range(3):
                nxt = []
                for v in frontier:
                    for w in adj[v]:
                        if not visited[w]:
                            visited[w] = 1
                            nxt.append(w)
                reached += len(nxt)
                frontier = nxt
                if not frontier:
                    break
            bad += n - reached
        return bad + dup

    def darts(self):
        d, k = self.d, self.k
        return [(t // d, k + self.heads[t], self.volt[t]) for t in range(self.m)]

    def step(self, T):
        rng = self.rng
        cur = self.cost
        if rng.random() < 0.5:
            t = rng.randrange(self.m)
            old = self.volt[t]
            new = rng.randrange(self.N)
            if new == old:
                return
            self.volt[t] = new
            c = self._cost()
            if c <= cur or rng.random() < math.exp((cur - c) / T):
                self.cost = c
            else:
                self.volt[t] = old
        else:
            t1 = rng.randrange(self.m)
            t2 = rng.randrange(self.m)
            if self.heads[t1] == self.heads[t2]:
                return
            h = self.heads
            h[t1], h[t2] = h[t2], h[t1]
            c = self._cost()
            if c <= cur or rng.random() < math.exp((cur - c) / T):
                self.cost = c
            else:
                h[t1], h[t2] = h[t2], h[t1]

    def run(self, steps, deadline, T):
        """Advance by up to `steps` moves; return True once the lift has zero defects."""
        if self.cost == 0:
            return True
        for k in range(steps):
            if (k & 15) == 0 and time.monotonic() > deadline:
                return False
            self.step(T)
            if self.cost == 0:
                return True
        return False


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 3.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    moore = lib.moore_bound(d, D)
    best_n, best = base_n, (base_n, base_e)

    # Jobs: (k base vertices per side, group order N, group), target order 2kN.
    jobs = []
    for k in (1, 2, 3):
        for N in range(moore // (2 * k), 1, -1):
            n_target = 2 * k * N
            if n_target <= best_n:
                break
            if n_target > moore:
                continue
            for _o, mul, _inv in _group_list(N, rng)[:3]:
                jobs.append({"k": k, "N": N, "n": n_target, "mul": mul,
                             "st": None, "dead": False, "score": float("inf")})
    jobs.sort(key=lambda j: j["n"])   # easier (smaller) targets first

    T = 0.6
    chunk = 100

    while jobs and time.monotonic() < deadline:
        for job in jobs:
            if time.monotonic() >= deadline:
                break
            if job["dead"] or job["n"] <= best_n:
                continue
            if job["st"] is None:
                mt = _mul_table(job["N"], job["mul"])
                job["st"] = _LiftSearch(job["k"], job["N"], mt, d, rng)
            st = job["st"]
            if st.run(chunk, deadline, T):
                k, N, mul = job["k"], job["N"], job["mul"]
                n, edges = lib.group_lift(2 * k, st.darts(), N, mul)
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best_n, best = n, (n, edges)
                job["dead"] = True
            else:
                job["score"] = st.cost / job["n"]

        jobs = [j for j in jobs if not j["dead"] and j["n"] > best_n]
        # Successive halving: once every job has been visited, keep the promising ones.
        if len(jobs) > 8 and all(j["st"] is not None for j in jobs):
            jobs.sort(key=lambda j: j["score"])
            jobs = jobs[: max(8, int(len(jobs) * 0.6))]

    return best

