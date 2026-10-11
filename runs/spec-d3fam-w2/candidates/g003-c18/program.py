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


# ------------------------------------------------ group candidates

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


# ------------------------------------------------ two-orbit difference covers

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


def _search_2orbit(d, D, rng, base_n, deadline):
    """Cayley-type 2-vertex lift search. Returns (n, edges) beating base_n, or None."""
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


# ------------------------------------------------ NEW: four-orbit lifts

class _Quad:
    """Four-orbit bipartite lift over a group G of order N.

    A-side orbits 0, 1 and B-side orbits 2, 3. Vertex (orbit o, x) has index o*N + x.
    Dart sets S[(i, j)] join a_i to b_j: (a_i, x) ~ (b_j, x*g) for g in S[(i, j)].
    Sizes are k, d-k, d-k, k, so every base vertex has degree exactly d.

    Left multiplication by G is an automorphism, so the distance from (o, x) to
    (o', y) equals the distance from (o, e) to (o', x^{-1} y). It is therefore enough
    to count vertices outside the 3-balls of the four identity vertices. Cost 0 means
    diameter <= 3.
    """

    def __init__(self, N, mt, k, d, rng):
        self.N = N
        self.mt = mt
        self.rng = rng
        self.blocks = [((0, 0), k), ((0, 1), d - k), ((1, 0), d - k), ((1, 1), k)]
        self.S = {key: rng.sample(range(N), sz) for key, sz in self.blocks}
        self.keys = [key for key, _ in self.blocks]
        self.cur = self.cost()

    def cost(self):
        N, mt = self.N, self.mt
        n = 4 * N
        adj = [[] for _ in range(n)]
        for (i, j), gs in self.S.items():
            a0, b0 = i * N, (2 + j) * N
            for g in gs:
                for x in range(N):
                    u = a0 + x
                    v = b0 + mt[x][g]
                    adj[u].append(v)
                    adj[v].append(u)
        total = 0
        for src in (0, N, 2 * N, 3 * N):
            seen = bytearray(n)
            seen[src] = 1
            frontier = [src]
            count = 1
            for _ in range(3):
                nxt = []
                for u in frontier:
                    for v in adj[u]:
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                count += len(nxt)
                frontier = nxt
            total += n - count
        return total

    def anneal(self, steps, T, stop):
        rng, N = self.rng, self.N
        for _ in range(steps):
            if self.cur == 0:
                return True
            if time.monotonic() > stop:
                return False
            lst = self.S[rng.choice(self.keys)]
            i = rng.randrange(len(lst))
            x = rng.randrange(N)
            if x in lst:
                continue
            old = lst[i]
            lst[i] = x
            new = self.cost()
            if new <= self.cur or rng.random() < math.exp(-(new - self.cur) / T):
                self.cur = new
            else:
                lst[i] = old
        return self.cur == 0

    def edges(self):
        N, mt = self.N, self.mt
        out = []
        for (i, j), gs in self.S.items():
            for g in gs:
                for x in range(N):
                    out.append((i * N + x, (2 + j) * N + mt[x][g]))
        return 4 * N, out


def _search_quad(d, D, rng, best_n, deadline):
    """Ascending search over N with 4N > best_n and 4N <= 2(d^2-d+1). Returns (n, edges) or None."""
    hi = (d * d - d + 1) // 2
    N = max(best_n // 4 + 1, d)
    best = None
    while N <= hi and time.monotonic() < deadline:
        now = time.monotonic()
        stop = min(deadline, now + max(1.0, 0.6 * (deadline - now)))
        states = []
        for _order, mul, _inv in _group_list(N, rng):
            mt = [[mul(x, y) for y in range(N)] for x in range(N)]
            k = rng.randrange(1, d)
            states.append(_Quad(N, mt, k, d, rng))
        found = None
        while found is None and states and time.monotonic() < stop:
            for st in states:
                if st.anneal(60, 0.7, stop):
                    found = st
                    break
                if time.monotonic() >= stop:
                    break
        if found is None:
            break
        n, edges = found.edges()
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
        N += 1
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

    best = (base_n, base_e)

    # Phase 1: two-orbit difference-cover search.
    t1 = start + 0.4 * (deadline - start)
    r2 = _search_2orbit(d, D, rng, base_n, t1)
    if r2 is not None and r2[0] > best[0] and lib.is_valid(r2[0], r2[1], d, D):
        best = r2

    # Phase 2: four-orbit search, seeded from the current best order.
    r4 = _search_quad(d, D, rng, best[0], deadline)
    if r4 is not None and r4[0] > best[0] and lib.is_valid(r4[0], r4[1], d, D):
        best = r4

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
