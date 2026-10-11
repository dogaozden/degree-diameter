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


# ------------------------------------------------ stage 1: difference covers
#
# Two base vertices with darts S give a bipartite Cayley-type lift of order 2|G|.
# Diameter <= 3 exactly when S S^{-1} = G. This is the earlier method, kept as a
# cheap first pass that reliably recovers the previous best.

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


def _cover_search(d, base_n, deadline, rng):
    """Return the best (n, edges) with n > base_n found by difference covers, or None."""
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
                if n > base_n and lib.is_valid(n, edges, d, D_GLOBAL):
                    best = (n, edges)
                    best_N = job["N"]
                    break
                job["dead"] = True
        jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]
    return best


# ------------------------------------ stage 2: annealed multi-vertex lifts
#
# Base: k A-vertices and k B-vertices, joined by d permutation layers, so every
# base vertex has d darts. Each dart (i, j) gets a group voltage g, joining
# A(i,x) to B(j, x*g). Left multiplication by G is an automorphism, so
# diameter <= 3 is checked only from the 2k representatives A(i,e), B(j,e).
# Cost = number of unreached (rep, vertex) pairs; annealed on voltages.

def _perm_base(k, d, rng):
    """Darts (i, j) from d random permutation layers: each vertex gets exactly d darts."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        darts.extend((i, p[i]) for i in range(k))
    return darts


def _groups_of(m, rng):
    """Cyclic group plus a few semidirect products Z_a x| Z_b with a*b = m."""
    out = [lib.cyclic_group(m)]
    for b in range(2, m + 1):
        if m % b:
            continue
        a = m // b
        if a < 2:
            continue
        rs = [r for r in range(1, a) if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a]
        rng.shuffle(rs)
        for r in rs[:2]:
            try:
                out.append(lib.semidirect_group(a, b, r))
            except ValueError:
                pass
    return out


def _mul_table(m, mul):
    return [[mul(x, g) for g in range(m)] for x in range(m)]


def _adjacency(k, m, darts, volts, M):
    n = 2 * k * m
    adj = [[] for _ in range(n)]
    for (i, j), g in zip(darts, volts):
        base_b = k * m + j * m
        for x in range(m):
            a = i * m + x
            b = base_b + M[x][g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _cost(adj, n, reps):
    """Total unreached pairs from the representatives within distance 3."""
    reach = [1 << v for v in range(n)]
    for _ in range(2):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    total = 0
    for s in reps:
        r = reach[s]
        for u in adj[s]:
            r |= reach[u]
        total += n - r.bit_count()
    return total


def _anneal(k, m, darts, M, rng, steps, deadline):
    n = 2 * k * m
    reps = [i * m for i in range(k)] + [k * m + j * m for j in range(k)]
    nd = len(darts)
    volts = [rng.randrange(m) for _ in range(nd)]
    cur = _cost(_adjacency(k, m, darts, volts, M), n, reps)
    for s in range(steps):
        if cur == 0:
            break
        if (s & 63) == 0 and time.monotonic() > deadline:
            break
        T = 3.0 * (0.2 / 3.0) ** (s / steps)
        e = rng.randrange(nd)
        old = volts[e]
        new = rng.randrange(m)
        if new == old:
            continue
        volts[e] = new
        c2 = _cost(_adjacency(k, m, darts, volts, M), n, reps)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
        else:
            volts[e] = old
    return volts if cur == 0 else None


def _edges(k, m, darts, volts, M):
    es = set()
    for (i, j), g in zip(darts, volts):
        for x in range(m):
            es.add((i * m + x, k * m + j * m + M[x][g]))
    return sorted(es)


def _sa_search(d, D, best_n, deadline, rng):
    """Return a valid (n, edges) with n > best_n, or None."""
    moore = lib.moore_bound(d, D)
    cache = {}

    def tables(m):
        if m not in cache:
            cache[m] = [_mul_table(order, mul)
                        for order, mul, _inv in _groups_of(m, rng)[:3]]
        return cache[m]

    def candidates(cur):
        out = []
        for k in (2, 3, 4):
            for m in range(cur // (2 * k) + 1, moore // (2 * k) + 1):
                n = 2 * k * m
                if cur < n <= moore:
                    out.append((n, k, m))
        out.sort()
        return out

    best = None
    cur = best_n
    while time.monotonic() < deadline:
        cs = candidates(cur)
        if not cs:
            break
        n, k, m = cs[rng.randrange(min(len(cs), 8))]
        M = rng.choice(tables(m))
        darts = _perm_base(k, d, rng)
        volts = _anneal(k, m, darts, M, rng, 2000, deadline)
        if volts is None:
            continue
        edges = _edges(k, m, darts, volts, M)
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
            cur = n
    return best


D_GLOBAL = 3


def build(d, D, seed, time_limit):
    global D_GLOBAL
    D_GLOBAL = D
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 3.0)
    deadline = start + total
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; the Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best_n, best_e = base_n, base_e

    cover = _cover_search(d, base_n, start + 0.3 * total, rng)
    if cover is not None and cover[0] > best_n and lib.is_valid(cover[0], cover[1], d, D):
        best_n, best_e = cover

    sa = _sa_search(d, D, best_n, deadline, rng)
    if sa is not None and sa[0] > best_n and lib.is_valid(sa[0], sa[1], d, D):
        best_n, best_e = sa

    return best_n, best_e
