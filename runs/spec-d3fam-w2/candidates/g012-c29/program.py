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


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


# ------------------------------------------------ p=1: difference covers

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


# ------------------------------------------------ p+p voltage lifts

class _LiftSearch:
    """Annealing over voltage assignments on a p+p base multigraph.

    Base A-vertices 0..p-1 and B-vertices p..2p-1. Each A-vertex has exactly d
    darts (j, g) and each B-vertex has exactly d darts in total, so the lift is
    d-regular. Left translations are automorphisms of the lift, so the lift has
    diameter <= 3 iff every base vertex (as source at identity) reaches the whole
    lift within 3 steps. The cost is the total number of unreached pairs over the
    2p sources, and it is zero exactly for valid diameter-3 lifts.
    """

    def __init__(self, p, N, mul, inv, d, rng):
        self.p, self.N, self.d, self.rng = p, N, d, rng
        self.mul = mul
        self.M = [[mul(x, y) for y in range(N)] for x in range(N)]
        self.ginv = [inv(g) for g in range(N)]
        self.total = 2 * p * N
        self.col = [0] * p
        self.rows = [None] * p
        for i in range(p):
            row, used = [], set()
            for _ in range(d):
                while True:
                    j = rng.randrange(p)
                    if self.col[j] < d:
                        break
                while True:
                    g = rng.randrange(N)
                    if (j, g) not in used:
                        break
                used.add((j, g))
                row.append([j, g])
                self.col[j] += 1
            self.rows[i] = row
        self.cost = self._cost()
        self.done = self.cost == 0

    def _nbrs(self, v):
        p, N, M = self.p, self.N, self.M
        u, x = divmod(v, N)
        if u < p:
            return [(p + j) * N + M[x][g] for j, g in self.rows[u]]
        j = u - p
        out = []
        ginv = self.ginv
        for i in range(p):
            for jj, g in self.rows[i]:
                if jj == j:
                    out.append(i * N + M[x][ginv[g]])
        return out

    def _cost(self):
        total = 0
        for u in range(2 * self.p):
            src = u * self.N
            seen = {src}
            frontier = [src]
            for _ in range(3):
                nxt = []
                for v in frontier:
                    for w in self._nbrs(v):
                        if w not in seen:
                            seen.add(w)
                            nxt.append(w)
                frontier = nxt
                if not frontier:
                    break
            total += self.total - len(seen)
        return total

    def run(self, steps, deadline, T):
        if self.done:
            return True
        rng, p, N, d = self.rng, self.p, self.N, self.d
        for s in range(steps):
            if self.cost == 0:
                break
            if (s & 15) == 0 and time.monotonic() > deadline:
                return False
            i = rng.randrange(p)
            k = rng.randrange(d)
            oj, og = self.rows[i][k]
            nj = rng.randrange(p)
            ng = rng.randrange(N)
            if nj == oj and ng == og:
                continue
            if nj != oj and self.col[nj] >= d:
                continue
            if any(rj == nj and rg == ng for idx, (rj, rg) in enumerate(self.rows[i]) if idx != k):
                continue
            self.rows[i][k] = [nj, ng]
            if nj != oj:
                self.col[oj] -= 1
                self.col[nj] += 1
            new = self._cost()
            delta = new - self.cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                self.cost = new
            else:
                self.rows[i][k] = [oj, og]
                if nj != oj:
                    self.col[nj] -= 1
                    self.col[oj] += 1
        if self.cost == 0:
            self.done = True
        return self.done

    def graph(self):
        darts = [(i, self.p + j, g) for i in range(self.p) for j, g in self.rows[i]]
        return lib.group_lift(2 * self.p, darts, self.N, self.mul)


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

    moore = lib.moore_bound(d, D)
    best_n, best = base_n, (base_n, base_e)

    jobs = []
    # p = 1: difference covers in a group of order N (2N vertices).
    hi1 = min(d * (d - 1) + 1, moore // 2)
    for N in range(hi1, d - 1, -1):
        if 2 * N <= best_n:
            break
        for _order, mul, inv in _group_list(N, rng):
            jobs.append({"kind": "cayley", "p": 1, "N": N, "n_total": 2 * N,
                         "mul": mul, "inv": inv, "st": None, "dead": False})
    # p = 2, 3: voltage lifts of p+p base graphs, searched by annealing.
    for p in (2, 3):
        hiN = moore // (2 * p)
        loN = best_n // (2 * p) + 1
        for N in range(hiN, max(loN, d) - 1, -1):
            if 2 * p * N <= best_n:
                continue
            for _order, mul, inv in _group_list(N, rng):
                jobs.append({"kind": "lift", "p": p, "N": N, "n_total": 2 * p * N,
                             "mul": mul, "inv": inv, "st": None, "dead": False})

    chunk_cayley = 1500
    chunk_lift = 200
    T_cayley = 0.6
    T_lift = 0.8

    try:
        while jobs and time.monotonic() < deadline:
            for job in list(jobs):
                if time.monotonic() >= deadline:
                    break
                if job["n_total"] <= best_n or job["dead"]:
                    continue
                if job["st"] is None:
                    if job["kind"] == "cayley":
                        R = _ratio_table(job["N"], job["mul"], job["inv"])
                        job["st"] = _Search(job["N"], R, d, rng)
                    else:
                        job["st"] = _LiftSearch(job["p"], job["N"], job["mul"],
                                                job["inv"], d, rng)
                st = job["st"]
                if job["kind"] == "cayley":
                    finished = st.run(chunk_cayley, deadline, T_cayley)
                else:
                    finished = st.run(chunk_lift, deadline, T_lift)
                if finished:
                    if job["kind"] == "cayley":
                        n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S],
                                                  job["N"], job["mul"])
                    else:
                        n, edges = st.graph()
                    if n > best_n and lib.is_valid(n, edges, d, D):
                        best = (n, edges)
                        best_n = n
                        break
                    job["dead"] = True
            jobs = [j for j in jobs if j["n_total"] > best_n and not j["dead"]]
    except Exception:
        pass

    return best

