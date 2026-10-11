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


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _mul_table(N, mul):
    """M[x][g] = x * g as a list of lists."""
    return [[mul(x, g) for g in range(N)] for x in range(N)]


# ------------------------------------------- phase 1: difference covers (k=1)

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


def _difference_cover_search(d, D, rng, cur_n, deadline):
    """Two base vertices, lift by G with S S^{-1} = G. Returns (n, edges) or None."""
    lo = cur_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return None
    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _o, mul, inv in _group_list(N, rng):
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
                n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S],
                                          job["N"], job["mul"])
                if n > cur_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]
    return best


# ---------------------------------- phase 2: four-vertex voltage lifts (k=2)
#
# Base: A = {0, 1}, B = {2, 3}. Darts (0,2) and (1,3) carry x voltages each,
# darts (0,3) and (1,2) carry d-x each, so every base vertex has degree d.
# Lifting by a group G of order N gives 4N vertices. The group acts by left
# multiplication, which is an automorphism of the lift and is transitive on
# each fiber. So the diameter is at most 3 iff the balls of radius 3 around
# the four identity vertices (u, e) cover everything. That check is cheap.

_PAIRS = ((0, 2), (1, 3), (0, 3), (1, 2))


def _lift_adjacency(N, M, darts):
    adj = [[] for _ in range(4 * N)]
    for u, v, g in darts:
        for x in range(N):
            a = u * N + x
            b = v * N + M[x][g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _defect(N, adj):
    """Total number of (source, vertex) pairs at distance > 3 over the 4 fiber sources."""
    size = 4 * N
    total = 0
    for u in range(4):
        s = u * N
        seen = {s}
        frontier = [s]
        for _ in range(3):
            nxt = []
            for a in frontier:
                for b in adj[a]:
                    if b not in seen:
                        seen.add(b)
                        nxt.append(b)
            frontier = nxt
        total += size - len(seen)
    return total


class _Lift:
    def __init__(self, N, M, d, x, rng):
        self.N = N
        self.M = M
        self.rng = rng
        self.counts = [x, x, d - x, d - x]
        self.stall = 0
        self._reset()

    def _reset(self):
        self.V = [self.rng.sample(range(self.N), m) for m in self.counts]
        self.score = self._eval()
        self.best_score = self.score
        self.stall = 0

    def darts(self):
        out = []
        for (u, v), vs in zip(_PAIRS, self.V):
            out.extend((u, v, g) for g in vs)
        return out

    def _eval(self):
        return _defect(self.N, _lift_adjacency(self.N, self.M, self.darts()))

    def _move(self, T):
        rng = self.rng
        vs = self.V[rng.randrange(4)]
        if not vs:
            self.stall += 1
            return
        i = rng.randrange(len(vs))
        g = rng.randrange(self.N)
        if g in vs:
            self.stall += 1
            return
        old = vs[i]
        vs[i] = g
        new = self._eval()
        delta = new - self.score
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            self.score = new
        else:
            vs[i] = old
        if self.score < self.best_score:
            self.best_score = self.score
            self.stall = 0
        else:
            self.stall += 1

    def run(self, steps, deadline, T=0.7):
        if self.score == 0:
            return True
        for k in range(steps):
            if (k & 15) == 0 and time.monotonic() > deadline:
                return False
            self._move(T)
            if self.score == 0:
                return True
            if self.stall > 4000:
                self._reset()
        return self.score == 0


def _voltage_search(d, D, rng, cur_n, deadline):
    """Search 4-vertex base voltage lifts over several groups. Returns (n, edges) or None."""
    lo = cur_n // 4 + 1
    hi = lib.moore_bound(d, D) // 4
    if lo > hi:
        return None
    jobs = []
    for N in range(lo, hi + 1):
        groups = _group_list(N, rng)
        cyc, rest = groups[0], groups[1:]
        rng.shuffle(rest)
        for _o, mul, _inv in [cyc] + rest[:2]:
            jobs.append({"N": N, "mul": mul, "x": rng.randrange(1, d),
                         "st": None, "dead": False})

    best = None
    best_N = lo - 1
    chunk = 150
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if job["N"] <= best_N or job["dead"]:
                continue
            if job["st"] is None:
                M = _mul_table(job["N"], job["mul"])
                job["st"] = _Lift(job["N"], M, d, job["x"], rng)
            st = job["st"]
            if st.run(chunk, deadline):
                n, edges = lib.group_lift(4, st.darts(), job["N"], job["mul"])
                if n > cur_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]
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

    # Only the diameter-3 regime is searched; the Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)

    # Phase 1: difference-cover lifts (parent's construction), a share of the budget.
    p1_deadline = start + 0.4 * total
    cand = _difference_cover_search(d, D, rng, best[0], p1_deadline)
    if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
        best = cand

    # Phase 2: four-vertex voltage lifts over cyclic and semidirect groups.
    cand = _voltage_search(d, D, rng, best[0], deadline)
    if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
        best = cand

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
