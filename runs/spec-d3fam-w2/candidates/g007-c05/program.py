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
# S S^{-1} = G. So the task is a "difference cover" of size d in a group G,
# giving order 2|G| with |G| <= d(d-1)+1.

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


# ------------------------------------------------ NEW: 2-switch annealing
#
# Not restricted to group structure. Start from a d-regular bipartite circulant
# on parts A = {0..N-1}, B = {N..2N-1} (a_x ~ b_{x+s}, s in S), then apply
# degree-preserving 2-switches (a1b1, a2b2) -> (a1b2, a2b1). Each switch keeps
# the graph simple, d-regular and bipartite. The cost is the number of unordered
# vertex pairs at distance > 3, computed with bitmask ball expansion. Metropolis
# acceptance with a geometric cooling schedule over the deadline.

def _bad_pairs3(adj, n):
    """Unordered pairs at distance > 3, via 3 rounds of bitmask ball expansion."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _two_switch_anneal(N, d, rng, deadline, T0=1.5, T1=0.05):
    """Return (cost, edge list over (a, b) with a, b in 0..N-1) for the best state seen."""
    n = 2 * N
    S = rng.sample(range(N), d)
    E = [(a, (a + s) % N) for a in range(N) for s in S]
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(N + b)
        adj[N + b].add(a)
    cur = _bad_pairs3(adj, n)
    best, bestE = cur, list(E)
    if cur == 0 or len(E) < 2:
        return best, bestE

    m = len(E)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T = T0
    it = 0
    while True:
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = (now - start) / span
            T = T0 * (T1 / T0) ** frac
        it += 1

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if b1 == b2:
            continue
        if (N + b2) in adj[a1] or (N + b1) in adj[a2]:
            continue

        adj[a1].discard(N + b1); adj[N + b1].discard(a1)
        adj[a2].discard(N + b2); adj[N + b2].discard(a2)
        adj[a1].add(N + b2); adj[N + b2].add(a1)
        adj[a2].add(N + b1); adj[N + b1].add(a2)
        E[i] = (a1, b2)
        E[j] = (a2, b1)

        new = _bad_pairs3(adj, n)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            if cur < best:
                best = cur
                bestE = list(E)
                if best == 0:
                    break
        else:
            adj[a1].discard(N + b2); adj[N + b2].discard(a1)
            adj[a2].discard(N + b1); adj[N + b1].discard(a2)
            adj[a1].add(N + b1); adj[N + b1].add(a1)
            adj[a2].add(N + b2); adj[N + b2].add(a2)
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return best, bestE


# ---------------------------------------------------------------- driver

def _group_search(d, base_n, rng, deadline):
    """Parent's Cayley-type search. Return (n, edges) of the best valid lift, or None."""
    D = 3
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    usable = max(1.0, 0.8 * time_limit - 2.0)
    deadline = start + usable
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best_n, best_e = base_n, base_e

    # Phase 1: Cayley-type group search (about 45% of the usable time).
    group_deadline = start + 0.45 * usable
    g = _group_search(d, base_n, rng, group_deadline)
    if g is not None and lib.is_valid(g[0], g[1], d, D) and g[0] > best_n:
        best_n, best_e = g

    # Phase 2: 2-switch annealing for N = |part| just above the current best.
    nmax = (d - 1) ** 2 + (d - 1) + 1        # Moore bound on one side
    N = best_n // 2 + 1
    while N <= nmax and time.monotonic() < deadline - 0.5:
        cost, E = _two_switch_anneal(N, d, rng, deadline)
        if cost != 0:
            break
        edges = [(a, N + b) for a, b in E]
        n = 2 * N
        if not lib.is_valid(n, edges, d, D):
            break
        best_n, best_e = n, edges
        N += 1

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return base_n, base_e
