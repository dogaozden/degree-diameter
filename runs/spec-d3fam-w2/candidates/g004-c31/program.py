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


# ------------------------------------------------ group groups and helpers

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


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


class _Search:
    """Resumable annealing for d distinct elements S with S S^{-1} = G.

    Keeps cnt[g] = number of ordered pairs (a, b) in S x S with a b^{-1} = g,
    and zeros = number of g with cnt[g] == 0.
    """

    def __init__(self, N, R, d, rng):
        self.N = N
        self.R = R
        self.d = d
        self.rng = rng
        self.S = rng.sample(range(N), d)
        self.cnt = [0] * N
        for a in self.S:
            for b in self.S:
                self.cnt[R[a][b]] += 1
        self.zeros = sum(1 for c in self.cnt if c == 0)
        self.done = self.zeros == 0

    def _apply(self, x, others, sign):
        cnt, R = self.cnt, self.R
        Rx = R[x]
        gs = [Rx[x]] + [Rx[b] for b in others] + [R[b][x] for b in others]
        if sign < 0:
            for g in gs:
                cnt[g] -= 1
                if cnt[g] == 0:
                    self.zeros += 1
        else:
            for g in gs:
                if cnt[g] == 0:
                    self.zeros -= 1
                cnt[g] += 1

    def _step(self, T):
        S = self.S
        i = self.rng.randrange(self.d)
        x = self.rng.randrange(self.N)
        if x in S:
            return
        old = S[i]
        others = S[:i] + S[i + 1:]
        before = self.zeros
        self._apply(old, others, -1)
        self._apply(x, others, +1)
        delta = self.zeros - before
        if delta <= 0 or self.rng.random() < math.exp(-delta / T):
            S[i] = x
        else:
            self._apply(x, others, -1)
            self._apply(old, others, +1)

    def run(self, steps, deadline, T):
        if self.done:
            return True
        for k in range(steps):
            if self.zeros == 0:
                break
            if (k & 127) == 0 and time.monotonic() > deadline:
                return False
            self._step(T)
        if self.zeros == 0:
            self.done = True
        return self.done


# ------------------------------------------- NEW: four-orbit voltage annealing
#
# Base graph: A0, A1 (ids 0, 1) and B0, B1 (ids 2, 3), with darts only from A
# to B, so the lift is bipartite. Each A vertex sends d darts, and the split
# k0 / d-k0 keeps every B vertex at degree exactly d. The darts carry group
# elements, and the cost is the number of vertex pairs at distance > 3 in the
# lift. Simulated annealing on those group elements searches for a cost of zero.

def _bad4(N, darts, mul, D):
    """Number of ordered-reachability misses (within distance D) for the 4-orbit lift."""
    n = 4 * N
    adj = [set() for _ in range(n)]
    for u, v, g in darts:
        uo, vo = u * N, v * N
        for x in range(N):
            a, b = uo + x, vo + mul(x, g)
            adj[a].add(b)
            adj[b].add(a)
    adjl = [list(s) for s in adj]
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adjl[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal4(d, D, N, mul, rng, end):
    """Anneal group voltages on the 4-vertex base until the lift has diameter <= D."""
    k0 = rng.randint(1, d - 1)
    darts = []
    for _ in range(k0):
        darts.append((0, 2, rng.randrange(N)))
    for _ in range(d - k0):
        darts.append((0, 3, rng.randrange(N)))
    for _ in range(d - k0):
        darts.append((1, 2, rng.randrange(N)))
    for _ in range(k0):
        darts.append((1, 3, rng.randrange(N)))

    cur = _bad4(N, darts, mul, D)
    T = 1.0
    while cur > 0 and time.monotonic() < end:
        i = rng.randrange(len(darts))
        u, v, _g = darts[i]
        g = rng.randrange(N)
        cand = darts[:i] + [(u, v, g)] + darts[i + 1:]
        c = _bad4(N, cand, mul, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            darts, cur = cand, c
        T = max(0.05, T * 0.999)
    return darts if cur == 0 else None


def _orbit_phase(d, D, best, rng, deadline):
    """Search for 4-orbit lifts of order 4N > current best, bumping N on each success."""
    best_n, best_e = best
    moore = lib.moore_bound(d, D)
    N = best_n // 4 + 1
    if N > moore // 4:
        return best
    groups = _group_list(N, rng)
    while time.monotonic() < deadline and N <= moore // 4:
        _order, mul, _inv = rng.choice(groups)
        end = min(deadline, time.monotonic() + 4.0)
        darts = _anneal4(d, D, N, mul, rng, end)
        if darts is not None:
            n, e = lib.group_lift(4, darts, N, mul)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, e
        N += 1
        if N <= moore // 4:
            groups = _group_list(N, rng)
    return best_n, best_e


# ------------------------------------- difference-cover phase (2-vertex base)

def _cover_phase(d, best, rng, deadline):
    best_n, best_e = best
    lo = best_n // 2 + 1          # need 2|G| > current best order
    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
    if lo > hi:
        return best

    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

    best_N = lo - 1
    chunk = 1500
    T = 0.6

    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if job["N"] <= best_N or job["dead"]:
                continue
            if job["st"] is None:
                R = _ratio_table(job["N"], job["mul"], job["inv"])
                job["st"] = _Search(job["N"], R, d, rng)
            st = job["st"]
            if st.run(chunk, deadline, T):
                n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S], job["N"], job["mul"])
                if n > best_n and lib.is_valid(n, edges, d, 3):
                    best_n, best_e = n, edges
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]

    return best_n, best_e


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.8 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)
    best = _cover_phase(d, best, rng, start + 0.4 * total)
    best = _orbit_phase(d, D, best, rng, deadline)
    return best
