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


# --------------------------------------- new: multi-base voltage lift annealing
#
# Base graph: A = {0, 1}, B = {2, 3}. Row and column sums must equal d, which
# forces the multiplicity matrix [[p, d-p], [d-p, p]]. Each dart carries a
# group voltage; the lift has 4|G| vertices. Voltages are annealed to minimise
# lib.bad_pairs(n, edges, 3), the number of vertex pairs at distance > 3.

def _anneal_lift(d, N, mul, rng, deadline, steps):
    """Try to find a diameter-3 lift over a group of order N. Return (n, edges) or None."""
    p = rng.randint(0, d)
    sizes = [((0, 2), p), ((0, 3), d - p), ((1, 2), d - p), ((1, 3), p)]
    blocks = [[uv, rng.sample(range(N), s)] for uv, s in sizes if s > 0]

    def evaluate():
        darts = [(uv[0], uv[1], g) for uv, gs in blocks for g in gs]
        n, edges = lib.group_lift(4, darts, N, mul)
        return n, edges, lib.bad_pairs(n, edges, 3)

    n, edges, cost = evaluate()
    T = 0.7
    for k in range(steps):
        if cost == 0:
            break
        if (k & 15) == 0 and time.monotonic() > deadline:
            return None
        bi = rng.randrange(len(blocks))
        gs = blocks[bi][1]
        j = rng.randrange(len(gs))
        x = rng.randrange(N)
        if x in gs:
            continue
        old = gs[j]
        gs[j] = x
        n2, e2, c2 = evaluate()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost, edges, n = c2, e2, n2
        else:
            gs[j] = old
    if cost == 0:
        return n, edges
    return None


def _anneal_phase(d, D, best_n, rng, deadline):
    """Round-robin annealing over (order, group) jobs with 4|G| > best_n. Return best (n, edges) or None."""
    moore = lib.moore_bound(d, D)
    lo4 = best_n // 4 + 1
    Nmax = moore // 4
    jobs = []
    for N in range(max(lo4, d), Nmax + 1):
        for _o, mul, _inv in _group_list(N, rng):
            jobs.append((N, mul))
    best = None
    cur_best = best_n
    while jobs and time.monotonic() < deadline:
        N, mul = jobs[rng.randrange(len(jobs))]
        if 4 * N <= cur_best:
            jobs = [j for j in jobs if 4 * j[0] > cur_best]
            continue
        res = _anneal_lift(d, N, mul, rng, deadline, 1500)
        if res is not None:
            n, edges = res
            if n > cur_best and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                cur_best = n
                jobs = [j for j in jobs if 4 * j[0] > cur_best]
    return best


# ------------------------------------- parent: Cayley difference-cover search

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


def _cayley_search(d, D, best_n, rng, deadline):
    """Two-vertex Cayley lifts (difference covers). Return (n, edges) or None."""
    lo = best_n // 2 + 1
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

    # Only the diameter-3 regime is searched; the Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best_n, best_e = base_n, base_e

    # Phase 1 (new construction): annealed multi-base voltage lifts.
    phase1_end = start + 0.6 * (deadline - start)
    try:
        res = _anneal_phase(d, D, best_n, rng, phase1_end)
        if res is not None and res[0] > best_n:
            best_n, best_e = res
    except Exception:
        pass

    # Phase 2 (parent construction): Cayley difference covers with the rest of the budget.
    try:
        res = _cayley_search(d, D, best_n, rng, deadline)
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            best_n, best_e = res
    except Exception:
        pass

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return base_n, base_e
