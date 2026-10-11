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


# ------------------------------------------------ stage 1: difference covers over groups

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


def _group_search(d, D, base_n, deadline, rng):
    """Parent-style search for a difference cover S (|S| = d) with S S^{-1} = G, giving 2|G| vertices."""
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


# ------------------------------------------------ stage 2: annealed non-group lifts

def _lift_graph(d, k, m, perms, shifts):
    """Bipartite lift: A-layers i*m+x, B-layers (k+j)*m+y. Dart (i, perms[t][i], shifts[t][i]) for t < d."""
    edges = []
    for t in range(d):
        p = perms[t]
        sh = shifts[t]
        for i in range(k):
            j = p[i]
            s = sh[i]
            ba = i * m
            bb = (k + j) * m
            for x in range(m):
                edges.append((ba + x, bb + (x + s) % m))
    return 2 * k * m, edges


def _lift_cost(n, k, m, edges):
    """Total number of unreached (source, vertex) pairs within distance 3, from one source per layer.

    The lift is invariant under translation in each layer, so this is zero iff diameter <= 3.
    """
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    total = 0
    for L in range(2 * k):
        src = L * m
        seen = {src}
        frontier = [src]
        for _ in range(3):
            nf = []
            for u in frontier:
                for v in adj[u]:
                    if v not in seen:
                        seen.add(v)
                        nf.append(v)
            frontier = nf
            if not frontier:
                break
        total += n - len(seen)
    return total


class _LiftState:
    def __init__(self, d, k, m, rng):
        self.d = d
        self.k = k
        self.m = m
        self.perms = [rng.sample(range(k), k) for _ in range(d)]
        self.shifts = [[rng.randrange(m) for _ in range(k)] for _ in range(d)]
        self.n, edges = _lift_graph(d, k, m, self.perms, self.shifts)
        self.cost = _lift_cost(self.n, k, m, edges)

    def step(self, T, rng):
        t = rng.randrange(self.d)
        i = rng.randrange(self.k)
        old = self.shifts[t][i]
        new = rng.randrange(self.m)
        if new == old:
            return
        self.shifts[t][i] = new
        n, edges = _lift_graph(self.d, self.k, self.m, self.perms, self.shifts)
        c = _lift_cost(n, self.k, self.m, edges)
        delta = c - self.cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            self.cost = c
        else:
            self.shifts[t][i] = old


def _anneal(d, D, best, deadline, rng):
    best_n, best_e = best
    cands = []
    for k in range(2, 7):
        mmin = max(2, best_n // (2 * k) + 1)
        mmax = (d * d - d + 1) // k
        for m in range(mmin, mmax + 1):
            cands.append((2 * k * m, k, m))
    cands.sort()
    states = [_LiftState(d, k, m, rng) for _n, k, m in cands[:30]
              if time.monotonic() < deadline]

    T = 0.7
    slice_steps = 150
    while states and time.monotonic() < deadline:
        for st in list(states):
            if time.monotonic() >= deadline:
                break
            if st.n <= best_n:
                states.remove(st)
                continue
            for _ in range(slice_steps):
                if st.cost == 0 or time.monotonic() >= deadline:
                    break
                st.step(T, rng)
            if st.cost == 0:
                n, edges = _lift_graph(d, st.k, st.m, st.perms, st.shifts)
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best_n, best_e = n, edges
                states.remove(st)
                states = [s for s in states if s.n > best_n]
    return best_n, best_e


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, 0.8 * time_limit - 2.0)
    deadline = start + budget
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)

    # Stage 1: parent's difference-cover search (keeps the d=11 gain over the base).
    res = _group_search(d, D, base_n, start + 0.3 * budget, rng)
    if res is not None and res[0] > best[0]:
        best = res

    # Stage 2: annealed random-shift lifts with k base vertices per side.
    if time.monotonic() < deadline:
        n, edges = _anneal(d, D, best, deadline, rng)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    return best
