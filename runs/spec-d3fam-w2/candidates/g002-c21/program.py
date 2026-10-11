import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 (q a prime power >= 3), or None."""
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except Exception:
            return None
    return None


def _fallback(d, D):
    """Safe graphs used as the starting point; each is verified by the caller."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D == 3:
        if lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)  # Moore-extremal
        cands = [c for c in (_araujo(d), _pg_best(d)) if c is not None]
        if cands:
            return max(cands, key=lambda g: g[0])
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------
# Difference-cover lifts: two base vertices, darts (a, b, s) for s in S, over a
# group G of order N. Diameter <= 3 exactly when S S^{-1} = G, giving order 2N.
# ----------------------------------------------------------------------------

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
    """R[x][y] = x * y^{-1}."""
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


def _diff_cover(d, D, lo, hi, rng, deadline):
    """Search groups of order in (lo..hi] for a difference cover; return (n, edges) or None."""
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
                if lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]
    return best


# ----------------------------------------------------------------------------
# Matching-rewire growth for diameter 3. Remove a matching R of d edges
# (u side 0, v side 1); add x on side 0 joined to all v, and y on side 1 joined
# to all u. Degrees stay <= d. Anneal R until the diameter is <= D.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
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
    return color


def _random_matching(Eo, d, rng):
    pool = list(Eo)
    rng.shuffle(pool)
    used = set()
    R = []
    for u, v in pool:
        if u in used or v in used:
            continue
        R.append((u, v))
        used.add(u)
        used.add(v)
        if len(R) == d:
            return R
    return None


def _rewire_build(n, Eo, R):
    Rkeys = {(min(u, v), max(u, v)) for u, v in R}
    out = [e for e in Eo if (min(e[0], e[1]), max(e[0], e[1])) not in Rkeys]
    x, y = n, n + 1
    for u, v in R:
        out.append((x, v))
        out.append((u, y))
    return n + 2, out


def _pair_search(n, E, d, D, deadline, rng):
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    col = _bipartition(n, adj)
    if any(col[u] == col[v] for u, v in E):
        return None
    Eo = [(u, v) if col[u] == 0 else (v, u) for u, v in E]
    if len(Eo) < d:
        return None
    R = _random_matching(Eo, d, rng)
    if R is None:
        return None

    def cost(RR):
        nn, ee = _rewire_build(n, Eo, RR)
        return lib.bad_pairs(nn, ee, D)

    c = cost(R)
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    while time.monotonic() < deadline:
        if c == 0:
            return _rewire_build(n, Eo, R)
        frac = (time.monotonic() - t_start) / span
        T = 1.0 * (0.05 ** frac)
        i = rng.randrange(d)
        cand = Eo[rng.randrange(len(Eo))]
        used = set()
        for j, (a, b) in enumerate(R):
            if j != i:
                used.add(a)
                used.add(b)
        if cand[0] in used or cand[1] in used:
            continue
        newR = list(R)
        newR[i] = cand
        c2 = cost(newR)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            R, c = newR, c2
    if c == 0:
        return _rewire_build(n, Eo, R)
    return None


def _pair_grow(n, E, d, D, deadline, rng):
    cur_n, cur_e = n, list(E)
    while time.monotonic() < deadline:
        res = _pair_search(cur_n, cur_e, d, D, deadline, rng)
        if res is None:
            break
        cur_n, cur_e = res
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    span = max(0.5, 0.85 * time_limit - 2.0)
    end = start + span
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Moore-extremal or non-target regimes: the fallback is final.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best_n, best_e = base_n, base_e

    # Phase 1: difference-cover lifts with orders above the current best.
    lo = best_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo <= hi:
        res = _diff_cover(d, D, lo, hi, rng, start + 0.55 * span)
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            best_n, best_e = res

    # Phase 2: rewire growth from the best graph found so far.
    n3, e3 = _pair_grow(best_n, best_e, d, D, end, random.Random(seed + 101))
    if n3 > best_n and lib.is_valid(n3, e3, d, D):
        best_n, best_e = n3, e3

    if not lib.is_valid(best_n, best_e, d, D):
        return base_n, base_e
    return best_n, best_e
