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
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 exactly when
# S S^{-1} = G. So the task is a "difference cover" of size d in a group G,
# which gives order 2|G| with |G| <= d(d-1)+1.

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


# ------------------------------------------- NEW: repair-annealing extension
#
# Given a bipartite base graph with parts A (local ids 0..M-1) and B, add one
# new vertex to each side and anneal edge sets to make the graph d-regular
# with diameter <= D. Cost = (number of pairs at distance > D) + (missing
# degree). Edge moves: add a random A-B non-edge, evicting one random edge at
# each endpoint that is already full. Adding an edge never increases the
# bad-pair count, so the search only needs to resolve the remaining defects.

def _bad_pairs(adj, n, D):
    """Number of unordered pairs at distance > D, from unified adjacency sets."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(M, adj, d, D, rng, deadline, T=0.5):
    """Repair adj (A = 0..M-1, B = M..2M-1, sets) in place. Return True on success."""
    n = 2 * M

    def cost():
        return _bad_pairs(adj, n, D) + sum(d - len(adj[v]) for v in range(n))

    f = cost()
    while f > 0:
        if time.monotonic() > deadline:
            return False
        defA = [v for v in range(M) if len(adj[v]) < d]
        defB = [M + j for j in range(M) if len(adj[M + j]) < d]
        x = rng.choice(defA) if defA and rng.random() < 0.5 else rng.randrange(M)
        y = rng.choice(defB) if defB and rng.random() < 0.5 else M + rng.randrange(M)
        if y in adj[x]:
            continue
        removed = []
        if len(adj[x]) >= d:
            removed.append((x, rng.choice(tuple(adj[x]))))
        if len(adj[y]) >= d:
            removed.append((y, rng.choice(tuple(adj[y]))))
        for p, q in removed:
            adj[p].discard(q)
            adj[q].discard(p)
        adj[x].add(y)
        adj[y].add(x)
        nf = cost()
        delta = nf - f
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            f = nf
        else:
            adj[x].discard(y)
            adj[y].discard(x)
            for p, q in removed:
                adj[p].add(q)
                adj[q].add(p)
    return True


def _two_color(n, edges):
    """Return a 0/1 colouring of a bipartite graph, or None if it is not bipartite."""
    adj = lib.adjacency(n, edges)
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


def _extend(base_n, base_e, d, D, rng, deadline):
    """Repeatedly add one vertex per side and repair; return the largest valid graph reached."""
    col = _two_color(base_n, base_e)
    if col is None:
        return base_n, base_e
    A = [v for v in range(base_n) if col[v] == 0]
    B = [v for v in range(base_n) if col[v] == 1]
    if len(A) != len(B) or not A:
        return base_n, base_e
    ia = {v: i for i, v in enumerate(A)}
    ib = {v: j for j, v in enumerate(B)}
    M = len(A)
    pairs = set()
    for u, v in base_e:
        if col[u] == 0:
            pairs.add((ia[u], ib[v]))
        else:
            pairs.add((ia[v], ib[u]))

    best_n, best_e = base_n, base_e
    while time.monotonic() < deadline:
        M2 = M + 1
        if 2 * M2 > lib.moore_bound(d, D):
            break
        adj = [set() for _ in range(2 * M2)]
        for i, j in pairs:
            adj[i].add(M2 + j)
            adj[M2 + j].add(i)
        if not _anneal(M2, adj, d, D, rng, deadline):
            break
        edges = [(i, v) for i in range(M2) for v in adj[i]]
        best_n, best_e = 2 * M2, edges
        pairs = {(i, v - M2) for i in range(M2) for v in adj[i]}
        M = M2
    return best_n, best_e


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, 0.88 * time_limit - 2.0)
    cay_deadline = start + 0.55 * budget
    deadline = start + budget
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Moore-extremal or trivially optimal cases are returned directly.
    if d < 3 or D < 3 or base_n >= lib.moore_bound(d, D):
        return base_n, base_e
    if D == 3 and lib.is_prime_power(d - 1):
        return base_n, base_e

    best_n, best_e = base_n, base_e

    if D == 3:
        lo = base_n // 2 + 1
        hi = d * (d - 1) + 1
        if lo <= hi:
            jobs = []
            for N in range(hi, lo - 1, -1):
                if N < d:
                    continue
                for _order, mul, inv in _group_list(N, rng):
                    jobs.append({"N": N, "mul": mul, "inv": inv, "st": None, "dead": False})

            best_N = lo - 1
            chunk = 1500
            T = 0.6
            while jobs and time.monotonic() < cay_deadline:
                for job in list(jobs):
                    if time.monotonic() >= cay_deadline:
                        break
                    if job["N"] <= best_N or job["dead"]:
                        continue
                    if job["st"] is None:
                        R = _ratio_table(job["N"], job["mul"], job["inv"])
                        job["st"] = _Search(job["N"], R, d, rng)
                    st = job["st"]
                    if st.run(chunk, cay_deadline, T):
                        n, edges = lib.group_lift(2, [(0, 1, g) for g in st.S], job["N"], job["mul"])
                        if n > best_n and lib.is_valid(n, edges, d, D):
                            best_n, best_e = n, edges
                            best_N = job["N"]
                            break
                        job["dead"] = True
                jobs = [j for j in jobs if j["N"] > best_N and not j["dead"]]

    # NEW stage: extend the best base found so far by repair annealing.
    ext_n, ext_e = _extend(best_n, best_e, d, D, rng, deadline)
    if ext_n > best_n and lib.is_valid(ext_n, ext_e, d, D):
        return ext_n, ext_e
    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return base_n, base_e
