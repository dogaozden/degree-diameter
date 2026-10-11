import itertools
import math
import random
import time

import lib

ITERS = 500            # annealing steps per (base, group) attempt
T_HOT = 2.0            # initial annealing temperature (unreached-pair units)
T_COLD = 0.1           # final annealing temperature
MAX_GROUPS = 10        # groups tried per (a, N) attempt
MAX_BASE = 6           # base vertices per side (a)
BUDGET0 = 1.5          # seconds per attempt in the first pass
BUDGET_CAP = 6.0       # cap on per-attempt seconds
GROUP_CACHE_MAX = 40   # cap on cached multiplication tables


# ----------------------------------------------------------------------------
# Safe baseline families (fast, validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts over a base multigraph with `a` vertices per side, each vertex
# of degree d, lifted over a finite group G of order N (semidirect products
# Z_m x| Z_k, including cyclic groups). Vertices A_i,x and B_j,y are indexed
# globally as i*N+x and (a+j)*N+y. Dart t = (i, j) with voltage g gives the
# edges A_i,x -- B_j,x*g for all x. Left multiplication by G is an
# automorphism of the lift, so the diameter is decided by BFS from the a + a
# base representatives A_i,e and B_j,e.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


_GROUP_CACHE = {}


def _group_tables(m, k, r, N):
    """Return (T, invs): T[x][g] = x*g and invs[g] = g^-1 for the group Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _GROUP_CACHE.get(key)
    if hit is None:
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        hit = (T, invs)
        if len(_GROUP_CACHE) < GROUP_CACHE_MAX:
            _GROUP_CACHE[key] = hit
    return hit


class _Lift:
    """Voltage lift of a d-regular bipartite base multigraph on a + a vertices."""

    def __init__(self, a, N, d, D, T, invs, rng):
        self.a, self.N, self.d, self.D = a, N, d, D
        self.T, self.invs = T, invs
        self.aN = a * N
        self.V = 2 * a * N
        # One dart per (layer, A-vertex): A_i goes to B_{perm_l[i]}.
        self.di, self.dj = [], []
        for _ in range(d):
            perm = list(range(a))
            rng.shuffle(perm)
            for i in range(a):
                self.di.append(i)
                self.dj.append(perm[i])
        self.nd = len(self.di)
        self.Aadj = [[] for _ in range(a)]
        self.Badj = [[] for _ in range(a)]
        self.pairs = {}
        for t in range(self.nd):
            self.Aadj[self.di[t]].append(t)
            self.Badj[self.dj[t]].append(t)
            self.pairs.setdefault((self.di[t], self.dj[t]), []).append(t)
        self.gv = [-1] * self.nd
        self.ginv = [0] * self.nd
        self.sources = [i * N for i in range(a)] + [(a + j) * N for j in range(a)]

    def clash(self, t, g):
        """True if voltage g on dart t would duplicate another dart's edges."""
        for s in self.pairs[(self.di[t], self.dj[t])]:
            if s != t and self.gv[s] == g:
                return True
        return False

    def set(self, t, g):
        self.gv[t] = g
        self.ginv[t] = self.invs[g]

    def init_random(self, rng):
        for t in range(self.nd):
            for _ in range(60):
                g = rng.randrange(self.N)
                if not self.clash(t, g):
                    self.set(t, g)
                    break
            else:
                return False
        return True

    def unreached(self):
        """Total count of (source, vertex) pairs at distance > D over base representatives."""
        T, aN, N, D, V = self.T, self.aN, self.N, self.D, self.V
        gv, ginv, di, dj = self.gv, self.ginv, self.di, self.dj
        Aadj, Badj = self.Aadj, self.Badj
        total = 0
        for src in self.sources:
            seen = bytearray(V)
            seen[src] = 1
            frontier = [src]
            reached = 1
            for _ in range(D):
                nxt = []
                for v in frontier:
                    if v < aN:
                        i, x = divmod(v, N)
                        row = T[x]
                        for t in Aadj[i]:
                            w = aN + dj[t] * N + row[gv[t]]
                            if not seen[w]:
                                seen[w] = 1
                                nxt.append(w)
                    else:
                        j, y = divmod(v - aN, N)
                        row = T[y]
                        for t in Badj[j]:
                            w = di[t] * N + row[ginv[t]]
                            if not seen[w]:
                                seen[w] = 1
                                nxt.append(w)
                reached += len(nxt)
                frontier = nxt
                if not frontier:
                    break
            total += V - reached
        return total

    def edges(self):
        out = []
        N, aN, T = self.N, self.aN, self.T
        for t in range(self.nd):
            i, j, g = self.di[t], self.dj[t], self.gv[t]
            for x in range(N):
                out.append((i * N + x, aN + j * N + T[x][g]))
        return out


def _anneal(L, rng, iters, deadline):
    """Simulated annealing over the voltages to drive unreached pairs to zero."""
    cur = L.unreached()
    if cur == 0:
        return True
    N = L.N
    for it in range(iters):
        if time.monotonic() > deadline:
            break
        t = rng.randrange(L.nd)
        new = rng.randrange(N)
        old = L.gv[t]
        if new == old or L.clash(t, new):
            continue
        L.set(t, new)
        v = L.unreached()
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            if cur == 0:
                return True
        else:
            L.set(t, old)
    return cur == 0


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for base size a; return a valid-diameter lift or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        T, invs = _group_tables(m, k, r, N)
        L = _Lift(a, N, d, D, T, invs, rng)
        if not L.init_random(rng):
            continue
        if _anneal(L, rng, ITERS, deadline):
            return L
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 5.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    lo = max(best_n + 1, int(0.48 * moore))

    # Candidate (total, a, N) with total = 2*a*N, ascending, random within ties.
    cands = []
    for a in range(1, MAX_BASE + 1):
        for N in range(max(d, 2), moore // (2 * a) + 1):
            tot = 2 * a * N
            if lo <= tot <= moore:
                cands.append((tot, a, N))
    rng.shuffle(cands)
    cands.sort(key=lambda c: c[0])

    budget = BUDGET0
    while time.monotonic() < deadline:
        pending = [c for c in cands if c[0] > best_n]
        if not pending:
            break
        success = False
        for tot, a, N in pending:
            now = time.monotonic()
            if now >= deadline:
                break
            if tot <= best_n:
                continue
            att_deadline = min(deadline, now + budget)
            L = _attempt(a, N, d, D, rng, att_deadline)
            if L is None:
                continue
            consider(2 * a * N, L.edges())
            if best_n >= tot:
                success = True
                break
        if not success:
            budget = min(BUDGET_CAP, budget * 1.5)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
