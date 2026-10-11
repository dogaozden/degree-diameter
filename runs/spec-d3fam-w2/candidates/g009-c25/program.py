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
# One-orbit lift: two base vertices a, b with darts (a, b, s), s in S, give
# a_x ~ b_{x s}. Diameter <= 3 exactly when S S^{-1} = G (difference cover).

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


def _cover_search(d, D, base_n, deadline, rng):
    """Phase A: difference covers of size d in groups of order just above base_n // 2."""
    lo = base_n // 2 + 1
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
                if n > base_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]
    return best


# ------------------------------------------- NEW: two-orbit (2+2) voltage lifts
#
# Base multigraph: A-vertices a0, a1 and B-vertices b0, b1. Dart sets
#   S00 (size k), S01 (size d-k), S10 (size d-k), S11 (size k)
# give the lift on G x {4 orbits}: a_i,x ~ b_j, x*s for s in S_ij. Every vertex
# has degree exactly d and the graph is bipartite with 4|G| vertices.
#
# Translation x -> t*x is an automorphism, so the diameter-3 test only needs
# the radius-3 balls of one source per orbit (a0, a1, b0, b1 at identity).
# The cost is the total number of unreached vertices over those 4 sources,
# and simulated annealing drives it to 0.

class _Lift:
    """Resumable annealing state for one (group, k) choice of a two-orbit lift."""

    def __init__(self, N, mul, MUL, INV, k, d, rng):
        self.N = N
        self.mul = mul
        self.MUL = MUL
        self.INV = INV
        self.d = d
        self.rng = rng
        self.dead = False
        self.S = [
            [rng.sample(range(N), k), rng.sample(range(N), d - k)],
            [rng.sample(range(N), d - k), rng.sample(range(N), k)],
        ]
        self.cost = self._cost()

    def _cost(self):
        N, MUL, INV, S = self.N, self.MUL, self.INV, self.S
        adjA = [[(j, s) for j in (0, 1) for s in S[i][j]] for i in (0, 1)]
        adjB = [[(i, s) for i in (0, 1) for s in S[i][j]] for j in (0, 1)]
        total = 0
        for src in (0, N, 2 * N, 3 * N):
            seen = {src}
            frontier = [src]
            for _ in range(3):
                nxt = []
                for v in frontier:
                    base, x = divmod(v, N)
                    if base < 2:
                        row = MUL[x]
                        nb = [(2 + j) * N + row[s] for j, s in adjA[base]]
                    else:
                        row = MUL[x]
                        nb = [i * N + row[INV[s]] for i, s in adjB[base - 2]]
                    for w in nb:
                        if w not in seen:
                            seen.add(w)
                            nxt.append(w)
                frontier = nxt
            total += 4 * N - len(seen)
        return total

    def step(self, T):
        rng = self.rng
        i = rng.randrange(2)
        j = rng.randrange(2)
        lst = self.S[i][j]
        t = rng.randrange(len(lst))
        g = rng.randrange(self.N)
        if g in lst:
            return
        old = lst[t]
        lst[t] = g
        c = self._cost()
        delta = c - self.cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            self.cost = c
        else:
            lst[t] = old

    def run(self, steps, T):
        for _ in range(steps):
            if self.cost == 0:
                return True
            self.step(T)
        return self.cost == 0


def _make_configs(d, N, rng, cap=6):
    """Random (group, k) states of order N, capped so each gets enough steps."""
    groups = _group_list(N, rng)[:4]
    tables = []
    for _order, mul, inv in groups:
        MUL = [[mul(x, y) for y in range(N)] for x in range(N)]
        INV = [inv(x) for x in range(N)]
        tables.append((mul, MUL, INV))
    pairs = [(gi, k) for gi in range(len(groups)) for k in range(1, d // 2 + 1)]
    rng.shuffle(pairs)
    cfgs = []
    for gi, k in pairs[:cap]:
        mul, MUL, INV = tables[gi]
        cfgs.append(_Lift(N, mul, MUL, INV, k, d, rng))
    return cfgs


def _lift_search(d, D, N, deadline, rng, floor_n):
    """Phase B: find the largest N with a valid two-orbit lift of order 4N > floor_n."""
    best = None
    T = 1.0
    chunk = 200
    N = max(N, d)
    while time.monotonic() < deadline:
        configs = _make_configs(d, N, rng)
        found = None
        while found is None and configs and time.monotonic() < deadline:
            for st in list(configs):
                if time.monotonic() >= deadline:
                    break
                if st.run(chunk, T):
                    darts = [(i, 2 + j, s) for i in (0, 1) for j in (0, 1) for s in st.S[i][j]]
                    n, edges = lib.group_lift(4, darts, N, st.mul)
                    if n > floor_n and lib.is_valid(n, edges, d, D):
                        found = (n, edges)
                        break
                    st.dead = True
            configs = [c for c in configs if not c.dead]
        if found is None:
            break
        best = found
        floor_n = found[0]
        N += 1
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    total = deadline - start
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Moore-extremal and out-of-regime cases return the construction directly.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)

    # Phase A: difference-cover lifts (order 2N).
    got = _cover_search(d, D, best[0], start + 0.3 * total, rng)
    if got is not None and got[0] > best[0] and lib.is_valid(got[0], got[1], d, D):
        best = got

    # Phase B: two-orbit voltage lifts (order 4N), aiming above the current best.
    got = _lift_search(d, D, best[0] // 4 + 1, deadline, rng, best[0])
    if got is not None and got[0] > best[0] and lib.is_valid(got[0], got[1], d, D):
        best = got

    return best
