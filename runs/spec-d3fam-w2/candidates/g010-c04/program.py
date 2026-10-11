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


# ------------------------------------------------ group helpers

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


# ------------------------------------------------ NEW: two-orbit-per-side lifts
#
# Base graph: A0, A1 on one side, B0, B1 on the other, with k[i][j] darts
# between A_i and B_j, where k = [[t, d-t], [d-t, t]]. Every base vertex then
# has degree exactly d. The lift over a group G has 4|G| vertices.
#
# Left multiplication x -> h*x is an automorphism of the lift, so each orbit
# is transitive. Thus diameter <= 3 holds iff a BFS of depth 3 from each of
# the four orbit identities reaches every vertex. The search is simulated
# annealing on the total number of unreached (source, target) pairs.

def _unreached(adj, n, s):
    """Number of vertices not within distance 3 of s."""
    seen = bytearray(n)
    seen[s] = 1
    frontier = [s]
    cnt = 1
    for _ in range(3):
        nf = []
        for v in frontier:
            for w in adj[v]:
                if not seen[w]:
                    seen[w] = 1
                    nf.append(w)
        cnt += len(nf)
        frontier = nf
        if not frontier:
            break
    return n - cnt


class _P2Search:
    """Resumable annealing over voltages for the two-orbit lift over a group of order N."""

    def __init__(self, N, MT, d, t, rng):
        self.N = N
        self.MT = MT          # MT[x][y] = x * y as a table
        self.d = d
        self.rng = rng
        k = [[t, d - t], [d - t, t]]
        self.V = [[rng.sample(range(N), k[i][j]) for j in range(2)] for i in range(2)]
        self.cost = self._cost()

    def _cost(self):
        N, MT = self.N, self.MT
        n = 4 * N
        adj = [[] for _ in range(n)]
        for i in range(2):
            for j in range(2):
                for g in self.V[i][j]:
                    for x in range(N):
                        a = i * N + x
                        b = (2 + j) * N + MT[x][g]
                        adj[a].append(b)
                        adj[b].append(a)
        total = 0
        for s in (0, N, 2 * N, 3 * N):
            total += _unreached(adj, n, s)
        return total

    def darts(self):
        return [(i, 2 + j, g) for i in range(2) for j in range(2) for g in self.V[i][j]]

    def run(self, steps, deadline, T):
        """Advance by up to `steps` moves; return True once every pair is within distance 3."""
        if self.cost == 0:
            return True
        rng, N = self.rng, self.N
        for k in range(steps):
            if (k & 15) == 0 and time.monotonic() > deadline:
                return False
            i = rng.randrange(2)
            j = rng.randrange(2)
            lst = self.V[i][j]
            idx = rng.randrange(len(lst))
            new = rng.randrange(N)
            if new in lst:
                continue
            old = lst[idx]
            lst[idx] = new
            c = self._cost()
            delta = c - self.cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                self.cost = c
                if c == 0:
                    return True
            else:
                lst[idx] = old
        return self.cost == 0


# ------------------------------------------------ parent: one-orbit Cayley search

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


def _run_p1(d, D, rng, best_n, best_e, deadline):
    """Parent's one-orbit Cayley search, used as the second phase."""
    lo = best_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return best_n, best_e

    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

    chunk = 1500
    T = 0.6
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if 2 * job["N"] <= best_n or job["dead"]:
                continue
            if job["st"] is None:
                R = _ratio_table(job["N"], job["mul"], job["inv"])
                job["st"] = _Search(job["N"], R, d, rng)
            st = job["st"]
            if st.run(chunk, deadline, T):
                n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S], job["N"], job["mul"])
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best_n, best_e = n, edges
                    break
                job["dead"] = True
        jobs = [j for j in jobs if 2 * j["N"] > best_n and not j["dead"]]
    return best_n, best_e


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

    best_n, best_e = base_n, base_e

    # Phase 1: two-orbit-per-side voltage lifts over groups of order N (4N vertices).
    phase1_end = start + 0.6 * (deadline - start)
    hi4 = lib.moore_bound(d, 3) // 4
    lo4 = max(d, best_n // 4 + 1)
    jobs = []
    for N in range(hi4, lo4 - 1, -1):
        groups = _group_list(N, rng)
        for _order, mul, inv in groups[:2]:
            MT = [[mul(x, y) for y in range(N)] for x in range(N)]
            jobs.append({"N": N, "mul": mul, "MT": MT, "st": None, "dead": False})

    chunk = 200
    T = 1.5
    while jobs and time.monotonic() < phase1_end:
        for job in list(jobs):
            if time.monotonic() >= phase1_end:
                break
            if 4 * job["N"] <= best_n or job["dead"]:
                continue
            if job["st"] is None:
                t = rng.randint(1, d - 1)
                job["st"] = _P2Search(job["N"], job["MT"], d, t, rng)
            st = job["st"]
            if st.run(chunk, phase1_end, T):
                n, edges = lib.group_lift(4, st.darts(), job["N"], job["mul"])
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best_n, best_e = n, edges
                    break
                job["dead"] = True
        jobs = [j for j in jobs if 4 * j["N"] > best_n and not j["dead"]]

    # Phase 2: parent's one-orbit Cayley search for the remaining time.
    best_n, best_e = _run_p1(d, D, rng, best_n, best_e, deadline)

    return best_n, best_e
