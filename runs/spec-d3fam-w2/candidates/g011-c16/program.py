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
# graph on G x {0,1} with a_x ~ b_{x s}. Diameter <= 3 holds when S S^{-1} = G.

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


# ------------------------------------------- NEW: biregular pair-cover annealing
#
# Build a d-regular bipartite graph on sides A and B (N vertices each) such that
# every two vertices on the same side have a common neighbour. Then any two
# same-side vertices are at distance <= 2, and any a in A and b in B are at
# distance <= 3 (b has a neighbour a' in A, and a' is within 2 of a). So the
# graph has diameter 3 and order 2N, and it needs no group structure.
#
# Cost = number of uncovered pairs inside A plus inside B. Moves are
# degree-preserving edge swaps, and each swap updates O(d) pair counters.

def _count_pairs(lst, cnt):
    """Increment cnt for every unordered pair of distinct entries in lst."""
    for i in range(len(lst)):
        p = lst[i]
        for j in range(i + 1, len(lst)):
            q = lst[j]
            if p < q:
                cnt[p][q] += 1
            else:
                cnt[q][p] += 1


class _Cover:
    def __init__(self, N, d, rng):
        self.N, self.d, self.rng = N, d, rng
        S = rng.sample(range(N), d)                      # circulant start
        self.NA = [[(a + s) % N for s in S] for a in range(N)]
        self.NB = [[] for _ in range(N)]
        self.EA, self.EB = [], []
        self.adj = [bytearray(N) for _ in range(N)]
        for a in range(N):
            for b in self.NA[a]:
                self.NB[b].append(a)
                self.EA.append(a)
                self.EB.append(b)
                self.adj[a][b] = 1
        self.cA = [[0] * N for _ in range(N)]
        self.cB = [[0] * N for _ in range(N)]
        for v in range(N):
            _count_pairs(self.NB[v], self.cA)
            _count_pairs(self.NA[v], self.cB)
        self.zA = sum(1 for a in range(N) for x in range(a + 1, N) if self.cA[a][x] == 0)
        self.zB = sum(1 for a in range(N) for x in range(a + 1, N) if self.cB[a][x] == 0)

    def _bA(self, a, x, dl):
        if a > x:
            a, x = x, a
        row = self.cA[a]
        old = row[x]
        row[x] = old + dl
        if old == 0:
            self.zA -= 1
        elif old + dl == 0:
            self.zA += 1

    def _bB(self, a, x, dl):
        if a > x:
            a, x = x, a
        row = self.cB[a]
        old = row[x]
        row[x] = old + dl
        if old == 0:
            self.zB -= 1
        elif old + dl == 0:
            self.zB += 1

    def _swap(self, i, j):
        """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Calling it again undoes the move."""
        EA, EB, NA, NB = self.EA, self.EB, self.NA, self.NB
        a1, b1, a2, b2 = EA[i], EB[i], EA[j], EB[j]
        for x in NB[b1]:
            if x != a1:
                self._bA(a1, x, -1)
                self._bA(a2, x, 1)
        for x in NB[b2]:
            if x != a2:
                self._bA(a2, x, -1)
                self._bA(a1, x, 1)
        for y in NA[a1]:
            if y != b1:
                self._bB(b1, y, -1)
                self._bB(b2, y, 1)
        for y in NA[a2]:
            if y != b2:
                self._bB(b2, y, -1)
                self._bB(b1, y, 1)
        NB[b1][NB[b1].index(a1)] = a2
        NB[b2][NB[b2].index(a2)] = a1
        NA[a1][NA[a1].index(b1)] = b2
        NA[a2][NA[a2].index(b2)] = b1
        adj = self.adj
        adj[a1][b1] = 0
        adj[a2][b2] = 0
        adj[a1][b2] = 1
        adj[a2][b1] = 1
        EB[i] = b2
        EB[j] = b1

    def step(self, T):
        rng = self.rng
        M = len(self.EA)
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            return
        a1, b1, a2, b2 = self.EA[i], self.EB[i], self.EA[j], self.EB[j]
        if a1 == a2 or b1 == b2 or self.adj[a1][b2] or self.adj[a2][b1]:
            return
        before = self.zA + self.zB
        self._swap(i, j)
        delta = self.zA + self.zB - before
        if delta > 0 and rng.random() >= math.exp(-delta / T):
            self._swap(i, j)

    def graph(self):
        N = self.N
        edges = [(a, N + b) for a in range(N) for b in self.NA[a]]
        return 2 * N, edges


def _cover_search(N, d, deadline, rng):
    """Anneal a pair-cover graph with N vertices per side; return (n, edges) or None."""
    c = _Cover(N, d, rng)
    t0 = time.monotonic()
    period = max(2.0, (deadline - t0) / 3.0)   # reheat a few times
    T0, T1 = 1.0, 0.12
    T = T0
    it = 0
    while c.zA + c.zB > 0:
        if (it & 127) == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            phase = ((now - t0) / period) % 1.0
            T = T0 * (T1 / T0) ** phase
        c.step(T)
        it += 1
    return c.graph()


# ---------------------------------------------------------------- driver

def _group_phase(d, base_n, rng, deadline):
    """Difference-cover search over groups; returns best (n, edges) or None."""
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
                if n > base_n and lib.is_valid(n, edges, d, D=3):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; the Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)
    best_n = base_n

    # Phase 1: group-based difference covers (fast, gives a strong start).
    grp = _group_phase(d, base_n, rng, start + 0.3 * total)
    if grp is not None and grp[0] > best_n and lib.is_valid(grp[0], grp[1], d, D):
        best = grp
        best_n = grp[0]

    # Phase 2: pair-cover annealing, trying one more vertex per side each time.
    hi = d * (d - 1) + 1
    N = best_n // 2 + 1
    while N <= hi and time.monotonic() < deadline - 0.5:
        res = _cover_search(N, d, deadline, rng)
        if res is None:
            break
        n, edges = res
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n
            N += 1
        else:
            break

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
