"""Search for difference-cover lifts with a two-sided cover condition.

Construction: two base vertices a, b with darts (a, b, s) for s in S give the
bipartite graph on G x {0,1} with a_x ~ b_{x s}. Diameter <= 3 holds when both
S S^{-1} = G (a-a and b-b distances) and S^{-1} S = G, which the parent only
enforced for the first. This version:
  * checks both conditions (needed for non-abelian G, and automatically equal for abelian G),
  * uses every semidirect product Z_m x| Z_k of order N as a candidate group,
  * builds tables lazily and restarts stalled annealing runs from fresh random sets,
  * drops every job with N <= the best order found so far, so time concentrates on larger N.
Every result is checked with lib.is_valid; the verified fallback is returned otherwise.
"""
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


def _groups(N, rng, cap):
    """Cyclic group of order N plus up to cap-1 random semidirect products Z_m x| Z_k with m*k = N."""
    extra = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                extra.append((m, k, r))
    rng.shuffle(extra)
    groups = [lib.cyclic_group(N)]
    for m, k, r in extra[:max(0, cap - 1)]:
        try:
            groups.append(lib.semidirect_group(m, k, r))
        except ValueError:
            pass
    return groups


def _tables(N, mul, inv):
    """Return [R] (abelian) or [R, L] (non-abelian), where R[x][y] = x y^{-1} and L[x][y] = x^{-1} y."""
    iv = [inv(x) for x in range(N)]
    R = [[mul(x, iv[y]) for y in range(N)] for x in range(N)]
    for x in range(N):
        for y in range(x + 1, N):
            if mul(x, y) != mul(y, x):
                L = [[mul(iv[x], y) for y in range(N)] for x in range(N)]
                return [R, L]
    return [R]


class _Search:
    """Resumable annealing for d distinct elements S covering G under every table.

    cnts[t][g] counts ordered pairs (a, b) in S x S with table_t[a][b] = g.
    cost = number of uncovered (table, g) entries. Restarts after stall_limit
    moves without improving the best cost seen since the last restart.
    """

    def __init__(self, N, tabs, d, rng, stall_limit=40000):
        self.N = N
        self.tabs = tabs
        self.d = d
        self.rng = rng
        self.stall_limit = stall_limit
        self.reset()

    def reset(self):
        self.S = self.rng.sample(range(self.N), self.d)
        self.T = self.rng.uniform(0.3, 0.8)
        self.cnts = []
        zeros = 0
        for Tb in self.tabs:
            cnt = [0] * self.N
            for a in self.S:
                Ta = Tb[a]
                for b in self.S:
                    cnt[Ta[b]] += 1
            self.cnts.append(cnt)
            zeros += sum(1 for c in cnt if c == 0)
        self.zeros = zeros
        self.best = zeros
        self.stall = 0

    def _apply(self, x, others, sign):
        """Add (sign=+1) or remove (sign=-1) all ordered pairs involving x."""
        for Tb, cnt in zip(self.tabs, self.cnts):
            Tx = Tb[x]
            gs = [Tx[x]]
            for b in others:
                gs.append(Tx[b])
                gs.append(Tb[b][x])
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

    def _step(self):
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
        if delta <= 0 or self.rng.random() < math.exp(-delta / self.T):
            S[i] = x
        else:
            self._apply(x, others, -1)
            self._apply(old, others, +1)

    def run(self, steps, deadline):
        """Advance by up to `steps` moves; return True once every table is fully covered."""
        for k in range(steps):
            if self.zeros == 0:
                return True
            if (k & 127) == 0 and time.monotonic() > deadline:
                break
            self._step()
            if self.zeros < self.best:
                self.best = self.zeros
                self.stall = 0
            else:
                self.stall += 1
                if self.stall > self.stall_limit:
                    self.reset()
        return self.zeros == 0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit - 3.0, time_limit - 8.0))
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; the Moore-extremal case is already optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    lo = base_n // 2 + 1           # need 2|G| > current best order
    hi = d * (d - 1) + 1           # hard bound for diameter-3 covers
    if lo > hi:
        return base_n, base_e

    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _groups(N, rng, cap=4):
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

    best = None
    best_N = lo - 1
    chunk = 3000

    while jobs and time.monotonic() < deadline:
        for job in jobs:
            if time.monotonic() >= deadline:
                break
            if job["N"] <= best_N or job["dead"]:
                continue
            if job["st"] is None:
                tabs = _tables(job["N"], job["mul"], job["inv"])
                job["st"] = _Search(job["N"], tabs, d, rng)
            st = job["st"]
            if st.run(chunk, deadline):
                n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S], job["N"], job["mul"])
                if n > base_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                else:
                    job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]

    if best is not None:
        return best
    return base_n, base_e
