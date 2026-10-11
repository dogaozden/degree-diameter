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


# ------------------------------------------------ new: 2+2 voltage lifts (cyclic)
#
# Base multigraph with two vertices on each side: A0, A1 and B0, B1 (ids 0,1,2,3).
# Dart multiplicities are [[p, d-p], [d-p, p]], so every base vertex has
# total degree d and the base is connected. Each dart carries a voltage in Z_m,
# and the lift has 4m vertices. The voltages are annealed on the number of
# pairs at distance > 3 (lib.bad_pairs), restarting with a fresh split p
# every few thousand moves.

def _voltage_attempt(d, m, rng, deadline):
    """Try to find voltages in Z_m giving diameter <= 3. Return (n, edges) or None."""
    N = 4 * m
    mul = lambda x, y: (x + y) % m
    restart_steps = 3000

    while time.monotonic() < deadline:
        p = rng.randrange(1, d)
        counts = [(0, 0, p), (0, 1, d - p), (1, 0, d - p), (1, 1, p)]
        slots = []
        for i, j, c in counts:
            for _ in range(c):
                slots.append((i, 2 + j))
        volt = [rng.randrange(m) for _ in slots]

        def lift(vs):
            return lib.group_lift(4, [(u, v, g) for (u, v), g in zip(slots, vs)], m, mul)[1]

        cur_edges = lift(volt)
        cur = lib.bad_pairs(N, cur_edges, 3)
        T = 1.0
        for step in range(restart_steps):
            if cur == 0:
                return N, cur_edges
            if (step & 15) == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(len(slots))
            old = volt[i]
            volt[i] = rng.randrange(m)
            ed = lift(volt)
            c = lib.bad_pairs(N, ed, 3)
            if c <= cur or rng.random() < math.exp(-(c - cur) / T):
                cur, cur_edges = c, ed
            else:
                volt[i] = old
            T = max(0.05, T * 0.9995)
        if cur == 0:
            return N, cur_edges
    return None


def _voltage_search(d, rng, best_n, deadline):
    """Find the largest m with a valid 2+2 lift, starting just above best_n."""
    m = best_n // 4 + 1
    mmax = lib.moore_bound(d, 3) // 4
    best = None
    while m <= mmax and time.monotonic() < deadline:
        now = time.monotonic()
        att = min(deadline, now + max(2.0, 0.6 * (deadline - now)))
        res = _voltage_attempt(d, m, rng, att)
        if res is None:
            break
        n, edges = res
        if n > best_n and lib.is_valid(n, edges, d, 3):
            best = (n, edges)
            best_n = n
            m += 1
        else:
            break
    return best


# ------------------------------------------------ Cayley-type bipartite lifts
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 exactly when
# S S^{-1} = G. So the task is a "difference cover" of size d in a group G,
# which gives order 2|G| with |G| <= d(d-1)+1.

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


def _difference_search(d, D, rng, best_n, deadline):
    """Parent's difference-cover search. Returns (n, edges) beating best_n, or None."""
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

    # Only the diameter-3 regime is searched; Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)

    # Phase 1: 2+2 voltage lifts over cyclic groups.
    split = start + 0.55 * (deadline - start)
    r = _voltage_search(d, rng, best[0], split)
    if r is not None and r[0] > best[0]:
        best = r

    # Phase 2: parent's difference-cover search with the remaining time.
    r = _difference_search(d, D, rng, best[0], deadline)
    if r is not None and r[0] > best[0] and lib.is_valid(r[0], r[1], d, D):
        best = r

    return best
