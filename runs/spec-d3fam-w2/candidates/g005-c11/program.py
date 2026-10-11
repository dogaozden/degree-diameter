"""Diameter-3 bipartite lifts over small groups, searched with an implicit coverage cost.

New in this version: a 2-orbit base graph. Two A-vertices and two B-vertices are
joined by darts whose group-element sets S_ij (|S_ij| = sz[i][j]) give a bipartite
lift with 4|G| vertices. Each row and column sums to d, so the degree is exact.

The diameter check is done without building the full graph. Left translation
(x -> h x) is an automorphism of the lift, so the diameter is at most 3 iff a
depth-3 BFS from (b, identity) reaches every vertex, for each of the 2P base
vertices b. The annealer minimises the total number of uncovered (b, vertex)
pairs. Cost is zero exactly when the lift has diameter at most 3. The one-orbit
case (P = 1) is the parent's difference-cover search, handled by the same code.
"""
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
        for r in rs[:4]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


class _Lift:
    """Annealing state: group-element sets S[i][j] with |S[i][j]| = sz[i][j].

    Vertex (b, x) is stored as index b*N + x. Identity is element 0 in both the
    cyclic and semidirect encodings. Edges: A_i,x ~ B_j,(x*g) for g in S[i][j].
    """

    def __init__(self, P, N, sz, M, I, rng):
        self.P, self.N, self.sz, self.M, self.I, self.rng = P, N, sz, M, I, rng
        self.S = [[rng.sample(range(N), sz[i][j]) if sz[i][j] else []
                   for j in range(P)] for i in range(P)]
        self.cells = [(i, j) for i in range(P) for j in range(P) if sz[i][j] > 0]
        self.cost = self._defect()
        self.done = self.cost == 0

    def _defect(self):
        """Total number of (base source, vertex) pairs not reached within 3 steps from (b, identity)."""
        P, N, M, I, S = self.P, self.N, self.M, self.I, self.S
        total_n = 2 * P * N
        Aadj = [[(P + j, S[i][j]) for j in range(P) if S[i][j]] for i in range(P)]
        Badj = [[(i, [I[g] for g in S[i][j]]) for i in range(P) if S[i][j]]
                for j in range(P)]
        total = 0
        for src in range(2 * P):
            seen = [False] * total_n
            seen[src * N] = True
            frontier = [src * N]
            reached = 1
            for _ in range(3):
                nxt = []
                for idx in frontier:
                    b, x = divmod(idx, N)
                    row = M[x]
                    if b < P:
                        for tb, gs in Aadj[b]:
                            base = tb * N
                            for g in gs:
                                t = base + row[g]
                                if not seen[t]:
                                    seen[t] = True
                                    nxt.append(t)
                    else:
                        for ab, igs in Badj[b - P]:
                            base = ab * N
                            for ig in igs:
                                t = base + row[ig]
                                if not seen[t]:
                                    seen[t] = True
                                    nxt.append(t)
                frontier = nxt
                reached += len(nxt)
            total += total_n - reached
        return total

    def run(self, steps, deadline, T):
        """Advance the anneal by up to `steps` moves; return True once the cost is zero."""
        if self.done:
            return True
        rng, N = self.rng, self.N
        for k in range(steps):
            if (k & 15) == 0 and time.monotonic() > deadline:
                return False
            i, j = rng.choice(self.cells)
            lst = self.S[i][j]
            t = rng.randrange(len(lst))
            x = rng.randrange(N)
            if x in lst:
                continue
            old = lst[t]
            lst[t] = x
            c = self._defect()
            delta = c - self.cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                self.cost = c
                if c == 0:
                    self.done = True
                    return True
            else:
                lst[t] = old
        return False


def _activate(spec, d, rng):
    """Turn a (order, P, N, mul, inv) spec into a live search job, or None if infeasible."""
    order, P, N, mul, inv = spec
    if P == 1:
        if d > N:
            return None
        sz = [[d]]
    else:
        opts = [a for a in range(1, d) if a <= N and d - a <= N]
        if not opts:
            return None
        a = rng.choice(opts)
        sz = [[a, d - a], [d - a, a]]
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    lift = _Lift(P, N, sz, M, I, rng)
    return {"order": order, "P": P, "N": N, "mul": mul, "sz": sz,
            "lift": lift, "steps": 0}


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    cap = lib.moore_bound(d, D)
    best_n, best_e = base_n, base_e
    best_order = base_n

    # Specs in descending target order: 2-orbit base (P=2) and 1-orbit base (P=1).
    specs = []
    for P in (2, 1):
        for N in range(cap // (2 * P), d - 1, -1):
            if 2 * P * N <= best_order:
                break
            for _o, mul, inv in _group_list(N, rng):
                specs.append((2 * P * N, P, N, mul, inv))
    specs.sort(key=lambda t: -t[0])

    POOL = 6
    CHUNK = 150
    STEP_BUDGET = 3000
    T = 0.8

    pool = []
    ptr = 0

    def refill():
        nonlocal ptr
        while len(pool) < POOL and ptr < len(specs):
            spec = specs[ptr]
            ptr += 1
            if spec[0] <= best_order:
                continue
            job = _activate(spec, d, rng)
            if job is not None:
                pool.append(job)

    while time.monotonic() < deadline:
        refill()
        if not pool:
            break
        for job in list(pool):
            if time.monotonic() >= deadline:
                break
            if job["order"] <= best_order:
                pool.remove(job)
                continue
            ok = job["lift"].run(CHUNK, deadline, T)
            job["steps"] += CHUNK
            if ok:
                P, N, sz, lift = job["P"], job["N"], job["sz"], job["lift"]
                darts = [(i, P + j, g)
                         for i in range(P) for j in range(P) for g in lift.S[i][j]]
                n, edges = lib.group_lift(2 * P, darts, N, job["mul"])
                if n > best_order and lib.is_valid(n, edges, d, D):
                    best_n, best_e = n, edges
                    best_order = n
                pool.remove(job)
            elif job["steps"] > STEP_BUDGET:
                pool.remove(job)

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return base_n, base_e
