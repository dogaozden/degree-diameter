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


# ------------------------------------------------ Cayley-type bipartite lifts

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


# ------------------------------------- NEW: matching-insertion growth routine
#
# In a d-regular bipartite graph, pick d-1 edges (a_i, b_i) forming a matching
# (distinct A-ends and distinct B-ends). Delete them, then add two new vertices
# x (side A) and y (side B): x joins every b_i, y joins every a_i, and x joins y.
# Every old vertex keeps its degree and x, y reach degree exactly d, so the
# result is again d-regular and bipartite on n+2 vertices. The diameter may
# break, so the matching is hill-climbed to minimise lib.bad_pairs.

def _two_color(n, edges):
    """Return a 0/1 colouring of a bipartite graph, or None if it has an odd cycle."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _grow_by_matching(n, edges, d, D, rng, deadline):
    """Return (n+2, edges') with the matching insertion repaired to diameter D, or None."""
    if d < 2 or not edges:
        return None
    color = _two_color(n, edges)
    if color is None:
        return None
    k = d - 1
    if len(edges) < k:
        return None
    oriented = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]

    def is_matching(idx):
        As, Bs = set(), set()
        for i in idx:
            a, b = oriented[i]
            if a in As or b in Bs:
                return False
            As.add(a)
            Bs.add(b)
        return True

    def build_edges(idx):
        rem = set(idx)
        new = [e for i, e in enumerate(edges) if i not in rem]
        x, y = n, n + 1
        for i in idx:
            a, b = oriented[i]
            new.append((x, b))
            new.append((y, a))
        new.append((x, y))
        return n + 2, new

    def score(idx):
        nn, ee = build_edges(idx)
        return lib.bad_pairs(nn, ee, D)

    # Random initial matching of size k.
    order = list(range(len(edges)))
    rng.shuffle(order)
    cur = []
    As, Bs = set(), set()
    for i in order:
        a, b = oriented[i]
        if a in As or b in Bs:
            continue
        cur.append(i)
        As.add(a)
        Bs.add(b)
        if len(cur) == k:
            break
    if len(cur) < k:
        return None

    cur_s = score(cur)
    while cur_s > 0:
        if time.monotonic() > deadline:
            return None
        j = rng.randrange(k)
        cand = rng.randrange(len(edges))
        if cand in cur:
            continue
        trial = cur[:]
        trial[j] = cand
        if not is_matching(trial):
            continue
        s = score(trial)
        if s <= cur_s:
            cur, cur_s = trial, s

    nn, ee = build_edges(cur)
    if lib.is_valid(nn, ee, d, D):
        return nn, ee
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + total
    search_deadline = start + 0.6 * total
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    lo = base_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return base_n, base_e

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

    while jobs and time.monotonic() < search_deadline:
        for job in list(jobs):
            if time.monotonic() >= search_deadline:
                break
            if job["N"] <= best_N or job["dead"]:
                continue
            if job["st"] is None:
                R = _ratio_table(job["N"], job["mul"], job["inv"])
                job["st"] = _Search(job["N"], R, d, rng)
            st = job["st"]
            if st.run(chunk, search_deadline, T):
                n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S], job["N"], job["mul"])
                if n > base_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]

    if best is not None:
        cur_n, cur_e = best
    else:
        cur_n, cur_e = base_n, base_e

    # Growth phase: repeatedly insert vertex pairs while time remains.
    while time.monotonic() < deadline:
        grown = _grow_by_matching(cur_n, cur_e, d, D, rng, deadline)
        if grown is None:
            break
        if grown[0] > cur_n:
            cur_n, cur_e = grown

    if cur_n > base_n and lib.is_valid(cur_n, cur_e, d, D):
        return cur_n, cur_e
    return base_n, base_e
