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


# ------------------------------------------------------------------
# Stage 1 (new): bi-Cayley lifts over abelian groups with TWO base
# vertices per side. Vertices are a_i(x) = i*N + x (i = 0,1) and
# b_j(y) = 2N + j*N + y (j = 0,1). For each pair (i, j) there is a set
# S_ij of size n_ij, with a_i(x) ~ b_j(x + s) for s in S_ij. The size
# matrix is [[a, d-a], [d-a, a]], so every vertex has degree exactly d.
# Translations are automorphisms, so distance <= 3 for all pairs reduces
# to checking the four sources a_0(0), a_1(0), b_0(0), b_1(0).
# The search is simulated annealing on the count of bad pairs.

def _abelian_list(N):
    """Abelian groups of order N as (m1, m2), element a*m2+b; m2 = 1 gives the cyclic group."""
    out = [(N, 1)]
    for m1 in range(2, N):
        if N % m1 == 0 and N // m1 >= 2:
            out.append((m1, N // m1))
    return out


def _table(m1, m2):
    """Addition and negation tables for Z_m1 x Z_m2."""
    N = m1 * m2

    def add(x, y):
        a, b = divmod(x, m2)
        c, e = divmod(y, m2)
        return ((a + c) % m1) * m2 + (b + e) % m2

    addt = [[add(x, y) for y in range(N)] for x in range(N)]
    negt = [0] * N
    for x in range(N):
        row = addt[x]
        for y in range(N):
            if row[y] == 0:
                negt[x] = y
                break
    return addt, negt


def _nbrs(v, N, S, addt, negt):
    side = v // N
    x = v - side * N
    out = []
    if side < 2:
        for j in range(2):
            base = 2 * N + j * N
            row = addt[x]
            for s in S[side][j]:
                out.append(base + row[s])
    else:
        j = side - 2
        for i in range(2):
            row = addt[x]
            for s in S[i][j]:
                out.append(i * N + row[negt[s]])
    return out


def _bad(N, S, addt, negt):
    """Number of (source, vertex) pairs at distance > 3 from the four orbit representatives."""
    total = 4 * N
    bad = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = {src}
        frontier = [src]
        for _ in range(3):
            nxt = []
            for v in frontier:
                for w in _nbrs(v, N, S, addt, negt):
                    if w not in seen:
                        seen.add(w)
                        nxt.append(w)
            frontier = nxt
        bad += total - len(seen)
    return bad


def _anneal(N, d, a, addt, negt, rng, deadline, cap):
    """Anneal the four difference sets. Returns S (2x2 lists) with zero bad pairs, or None."""
    sz = [[a, d - a], [d - a, a]]
    S = [[rng.sample(range(N), sz[i][j]) for j in range(2)] for i in range(2)]
    cost = _bad(N, S, addt, negt)
    T = 0.8
    for step in range(cap):
        if cost == 0:
            return S
        if (step & 15) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(2)
        j = rng.randrange(2)
        L = S[i][j]
        if not L or len(L) >= N:
            continue
        k = rng.randrange(len(L))
        x = rng.randrange(N)
        if x in L:
            continue
        old = L[k]
        L[k] = x
        c = _bad(N, S, addt, negt)
        if c <= cost or rng.random() < math.exp(-(c - cost) / T):
            cost = c
        else:
            L[k] = old
    return S if cost == 0 else None


def _edges_from(N, S, addt):
    e = []
    for i in range(2):
        for j in range(2):
            for s in S[i][j]:
                for x in range(N):
                    e.append((i * N + x, 2 * N + j * N + addt[x][s]))
    return 4 * N, e


def _bi_search(d, D, base_n, deadline, rng, hi):
    """Climb the order 4N through bi-Cayley lifts. Returns the best validated (n, edges) or None."""
    best = None
    N = base_n // 4 + 1
    while N <= hi and time.monotonic() < deadline:
        groups = _abelian_list(N)
        found = None
        while found is None and time.monotonic() < deadline:
            m1, m2 = rng.choice(groups)
            a = rng.randrange(1, d)
            if max(a, d - a) > N:
                continue
            addt, negt = _table(m1, m2)
            S = _anneal(N, d, a, addt, negt, rng, deadline, 2500)
            if S is not None:
                found = (addt, S)
        if found is None:
            break
        addt, S = found
        n, edges = _edges_from(N, S, addt)
        if not lib.is_valid(n, edges, d, D):
            break
        best = (n, edges)
        N += 1
    return best


# ------------------------------------------------------------------
# Stage 2 (kept as a safe fallback): Cayley-type difference covers.
# Two base vertices a, b with darts (a, b, s) for s in S give a graph
# on G x {0,1} of order 2|G| and diameter at most 3 when S S^{-1} = G.

def _group_list(N, rng):
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


def _cayley_stage(d, D, base_n, deadline, rng):
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


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.8 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 4 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)

    # Stage 1: bold bi-Cayley lifts with two base vertices per side.
    stage1_end = start + 0.35 * total
    hi4 = lib.moore_bound(d, D) // 4
    r1 = _bi_search(d, D, best[0], stage1_end, rng, hi4)
    if r1 is not None and r1[0] > best[0] and lib.is_valid(r1[0], r1[1], d, D):
        best = r1

    # Stage 2: difference-cover fallback for the remaining time.
    r2 = _cayley_stage(d, D, best[0], deadline, rng)
    if r2 is not None and r2[0] > best[0] and lib.is_valid(r2[0], r2[1], d, D):
        best = r2

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
