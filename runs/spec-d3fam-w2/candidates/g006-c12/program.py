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


# ------------------------------------------------ NEW: two-orbit lifts, orbit-BFS cost
#
# Base graph: A0, A1 (ids 0,1) and B0, B1 (ids 2,3) with darts of multiplicity
# p, d-p, d-p, p between the four pairs (each vertex has degree exactly d).
# Lift over a group G of order N: A_{i,x} ~ B_{j, x g} for each dart (i,j,g).
# Left multiplication is an automorphism, so the diameter-3 test reduces to
# BFS from the four representatives (t, identity). The graph has order 4N and
# is bipartite by construction. The search anneals the voltages to drive the
# number of vertices beyond distance 3 from the representatives to zero.

def _k2_cost(N, mt, inv, darts):
    """Total number of (representative, vertex) pairs at distance > 3 (0 = valid)."""
    total = 4 * N
    bad = 0
    for r in range(4):
        start = r * N
        seen = {start}
        frontier = [start]
        for _ in range(3):
            nxt = []
            for v in frontier:
                t, x = divmod(v, N)
                if t < 2:
                    row = mt[x]
                    for j in (2, 3):
                        for g in darts[(t, j)]:
                            w = j * N + row[g]
                            if w not in seen:
                                seen.add(w)
                                nxt.append(w)
                else:
                    for i in (0, 1):
                        for g in darts[(i, t)]:
                            w = i * N + mt[x][inv[g]]
                            if w not in seen:
                                seen.add(w)
                                nxt.append(w)
            frontier = nxt
            if not frontier:
                break
        bad += total - len(seen)
    return bad


def _prepare_tables(N, groups):
    """For each group of order N, return (mul, multiplication table, inverse table)."""
    tabs = []
    for _order, mul, inv in groups:
        mt = [[mul(x, y) for y in range(N)] for x in range(N)]
        iv = [inv(x) for x in range(N)]
        tabs.append((mul, mt, iv))
    return tabs


def _k2_search(N, d, tables, rng, deadline):
    """Anneal voltages for the 2x2 base. Returns (darts, mul) or None on timeout."""
    p = rng.randrange(1, d)
    m = {(0, 2): p, (0, 3): d - p, (1, 2): d - p, (1, 3): p}
    keys = list(m)
    while time.monotonic() < deadline:
        mul, mt, inv = rng.choice(tables)
        darts = {k: rng.sample(range(N), m[k]) for k in keys}
        cur = _k2_cost(N, mt, inv, darts)
        T = 2.0
        for step in range(40000):
            if cur == 0:
                return darts, mul
            if (step & 31) == 0 and time.monotonic() > deadline:
                return None
            k = keys[rng.randrange(4)]
            lst = darts[k]
            idx = rng.randrange(len(lst))
            new = rng.randrange(N)
            if new in lst:
                continue
            old = lst[idx]
            lst[idx] = new
            c = _k2_cost(N, mt, inv, darts)
            if c <= cur or rng.random() < math.exp(-(c - cur) / T):
                cur = c
            else:
                lst[idx] = old
            T = max(0.05, T * 0.9998)
    return None


# ------------------------------------------------ Cayley-type one-orbit lifts (parent)

class _Search:
    """Resumable annealing for d distinct elements S with S S^{-1} = G."""

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


def _ratio_table(N, mul, inv):
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _k1_search(d, D, rng, deadline, best_n):
    """Difference-cover search over groups; returns (n, edges) beating best_n, or None."""
    lo = best_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return None
    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

    best = None
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
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]
    return best


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

    best = None
    best_n = base_n
    moore = lib.moore_bound(d, D)

    # Phase 1: two-orbit lifts of order 4N, trying increasing N.
    N = base_n // 4 + 1
    while 4 * N <= moore and time.monotonic() < deadline:
        now = time.monotonic()
        att_deadline = now + max(1.0, 0.6 * (deadline - now))
        tables = _prepare_tables(N, _group_list(N, rng))
        res = _k2_search(N, d, tables, rng, min(att_deadline, deadline))
        if res is None:
            break
        darts, mul = res
        edge_darts = [(i, j, g) for (i, j), lst in darts.items() for g in lst]
        n, edges = lib.group_lift(4, edge_darts, N, mul)
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n
        else:
            break
        N += 1

    # Phase 2: remaining time on the one-orbit difference-cover search.
    if time.monotonic() < deadline:
        r = _k1_search(d, D, rng, deadline, best_n)
        if r is not None and r[0] > best_n:
            best = r
            best_n = r[0]

    if best is not None:
        return best
    return base_n, base_e
