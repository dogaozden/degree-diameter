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


# ------------------------------------------------ Family A: 2-vertex Cayley lifts
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Diameter <= 3 when S S^{-1} = G.

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


def _all_groups(N):
    """Cyclic group plus every semidirect Z_m x| Z_k of order N that passes the checks."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
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


def _difference_cover_search(d, D, rng, deadline, best_n):
    """Return (n, edges) beating best_n from 2-vertex Cayley lifts, or None."""
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


# ------------------------------------------------ Family B: 4-vertex voltage lifts
#
# Base graph: A = {0, 1}, B = {2, 3}. Darts (0,2) x times, (0,3) d-x times,
# (1,2) d-x times, (1,3) x times. Every base vertex then has total degree d,
# and the lift over a group of order N has 4N vertices. Voltages are found by
# hill climbing on the number of pairs at distance > 3.

_FAMILY_B_KEYS = [(0, 2), (0, 3), (1, 2), (1, 3)]


class _Hill:
    def __init__(self, N, mul, d, x, rng):
        self.N = N
        self.mul = mul
        self.rng = rng
        sizes = {(0, 2): x, (0, 3): d - x, (1, 2): d - x, (1, 3): x}
        self.fam = {key: rng.sample(range(N), sizes[key]) for key in _FAMILY_B_KEYS}
        self.cur = self._score()

    def darts(self):
        return [(u, v, g) for (u, v) in _FAMILY_B_KEYS for g in self.fam[(u, v)]]

    def _score(self):
        n, edges = lib.group_lift(4, self.darts(), self.N, self.mul)
        return lib.bad_pairs(n, edges, 3)

    def step(self):
        key = self.rng.choice(_FAMILY_B_KEYS)
        gs = self.fam[key]
        i = self.rng.randrange(len(gs))
        g_new = self.rng.randrange(self.N)
        if g_new in gs:
            return
        old = gs[i]
        gs[i] = g_new
        s = self._score()
        if s <= self.cur:
            self.cur = s
        else:
            gs[i] = old


def _four_base_search(d, D, rng, deadline, best_n):
    """Return (n, edges) beating best_n from 4-vertex lifts, or None."""
    n_moore = lib.moore_bound(d, D)
    Nmax = n_moore // 4
    Nmin = best_n // 4 + 1
    if Nmin > Nmax:
        return None

    jobs = []
    for N in range(Nmax, Nmin - 1, -1):
        for group in _all_groups(N):
            _order, mul, _inv = group
            for x in range(1, d):
                if x <= N and d - x <= N:
                    jobs.append({"N": N, "mul": mul, "x": x, "st": None})

    best = None
    best_n_cur = best_n
    chunk = 40
    active = jobs

    while active and time.monotonic() < deadline:
        for job in list(active):
            if time.monotonic() >= deadline:
                break
            if 4 * job["N"] <= best_n_cur:
                active.remove(job)
                continue
            if job["st"] is None:
                job["st"] = _Hill(job["N"], job["mul"], d, job["x"], rng)
            st = job["st"]
            for _ in range(chunk):
                if st.cur == 0 or time.monotonic() >= deadline:
                    break
                st.step()
            if st.cur == 0:
                n, edges = lib.group_lift(4, st.darts(), job["N"], job["mul"])
                if n > best_n_cur and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_n_cur = n
                active.remove(job)
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.8 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best_n, best_e = base_n, base_e

    # Family A gets the first 60% of the budget; family B gets the rest.
    a_deadline = start + 0.6 * total
    res = _difference_cover_search(d, D, rng, a_deadline, best_n)
    if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
        best_n, best_e = res

    res = _four_base_search(d, D, rng, deadline, best_n)
    if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
        best_n, best_e = res

    return best_n, best_e
