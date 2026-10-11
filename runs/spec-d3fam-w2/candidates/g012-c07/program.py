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
        return lib.haar_graph(d, range(d))              # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)    # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)        # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------ Cayley-type bipartite lifts
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 whenever
# S S^{-1} = G (a "difference cover"). Each vertex has degree |S| = d, and
# there are no loops or duplicate edges since the elements of S are distinct.
#
# This version differs from the annealing parent in two ways:
#   * the search is tabu search with best-improvement moves over sampled
#     candidate swaps (not Metropolis acceptance), with random perturbation
#     after stalls;
#   * the group pool always includes the abelian direct products Z_m x Z_k
#     (r = 1), which the parent's random truncation could drop.

def _groups(N, rng, cap):
    """Cyclic group of order N, plus up to `cap` semidirect/direct products per factorization.

    The direct product (r = 1) is listed first for each factorization.
    """
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rs.sort(key=lambda r: (r != 1, rng.random()))
        for r in rs[:cap]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


class _Tabu:
    """Tabu search for d distinct elements S with S S^{-1} = G.

    cnt[g] counts ordered pairs (a, b) in S x S with a b^{-1} = g.
    cost = number of g with cnt[g] == 0 (uncovered elements). Cost 0 means S is a cover.
    """

    def __init__(self, N, R, d, rng):
        self.N = N
        self.R = R
        self.d = d
        self.rng = rng
        self.S = rng.sample(range(N), d)
        self.tabu = [0] * N
        self.it = 0
        self.stall = 0
        self._rebuild()
        self.best = self.cost
        self.done = self.cost == 0

    def _rebuild(self):
        cnt = [0] * self.N
        R, S = self.R, self.S
        for a in S:
            Ra = R[a]
            for b in S:
                cnt[Ra[b]] += 1
        self.cnt = cnt
        self.cost = sum(1 for c in cnt if c == 0)

    def _pairs(self, x, others):
        """Group elements from ordered pairs involving x (with itself and with others)."""
        Rx = self.R[x]
        out = [Rx[x]]
        for b in others:
            out.append(Rx[b])
            out.append(self.R[b][x])
        return out

    def _remove(self, x, others):
        cnt = self.cnt
        for g in self._pairs(x, others):
            cnt[g] -= 1
            if cnt[g] == 0:
                self.cost += 1

    def _add(self, x, others):
        cnt = self.cnt
        for g in self._pairs(x, others):
            if cnt[g] == 0:
                self.cost -= 1
            cnt[g] += 1

    def _step(self):
        self.it += 1
        S, N, d, rng = self.S, self.N, self.d, self.rng
        cand_per = min(N, 24)
        best_val = None
        best_move = None
        ties = 0
        cnt = self.cnt
        for i in range(d):
            old = S[i]
            others = S[:i] + S[i + 1:]
            self._remove(old, others)
            base = self.cost
            for _ in range(cand_per):
                x = rng.randrange(N)
                if x in S:
                    continue
                seen = set()
                gain = 0
                for g in self._pairs(x, others):
                    if cnt[g] == 0 and g not in seen:
                        gain += 1
                        seen.add(g)
                val = base - gain
                # Tabu unless the move beats the best cost seen since the last restart.
                if self.tabu[x] > self.it and val >= self.best:
                    continue
                if best_val is None or val < best_val:
                    best_val = val
                    best_move = (i, x)
                    ties = 1
                elif val == best_val:
                    ties += 1
                    if rng.randrange(ties) == 0:
                        best_move = (i, x)
            self._add(old, others)
        if best_move is None:
            return
        i, x = best_move
        old = S[i]
        others = S[:i] + S[i + 1:]
        self._remove(old, others)
        S[i] = x
        self._add(x, others)
        self.tabu[old] = self.it + 2 * d + 3
        if self.cost < self.best:
            self.best = self.cost
            self.stall = 0
        else:
            self.stall += 1
        if self.stall > 300:
            # Random perturbation to escape the basin.
            for _ in range(2):
                j = rng.randrange(d)
                c = rng.randrange(N)
                if c not in S:
                    S[j] = c
            self._rebuild()
            self.best = self.cost
            self.stall = 0

    def run(self, steps, deadline):
        """Advance by up to `steps` moves; return True once S is a difference cover."""
        if self.done:
            return True
        for _ in range(steps):
            if self.cost == 0:
                break
            if time.monotonic() > deadline:
                return False
            self._step()
        if self.cost == 0:
            self.done = True
        return self.done


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; the Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    lo = base_n // 2 + 1          # need 2|G| > current best order
    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
    if lo > hi:
        return base_n, base_e

    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _groups(N, rng, cap=2):
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

    best = None
    best_N = lo - 1
    chunk = 300

    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if job["N"] <= best_N or job["dead"]:
                continue
            if job["st"] is None:
                R = _ratio_table(job["N"], job["mul"], job["inv"])
                job["st"] = _Tabu(job["N"], R, d, rng)
            st = job["st"]
            if st.run(chunk, deadline):
                n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S],
                                          job["N"], job["mul"])
                if n > base_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
