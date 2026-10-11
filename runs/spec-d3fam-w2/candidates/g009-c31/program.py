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
# graph on G x {0,1} with a_x ~ b_{x s}. Diameter 3 holds when S S^{-1} = G.
# This phase finds a difference cover of size d in a group of order N.

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


def _cayley_search(d, D, rng, deadline, base_n):
    """Search difference covers over candidate groups; return the best valid (n, edges) or None."""
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


# ------------------------------------------ NEW: pair insertion + switch annealing
#
# Idea: take a valid graph on n vertices and append one A-vertex u and one
# B-vertex w. Each of u, w is made degree d by "splitting" existing edges:
# an edge (a,b) becomes (u,b) and (a,w), which keeps every old degree fixed.
# The result is bipartite with max degree d but may have bad pairs. Then a
# degree-preserving double-edge-switch annealing on the bad-pair count tries
# to repair it to diameter 3. Each successful repair adds 2 vertices.

def _two_color(n, edges):
    """Return a 0/1 side per vertex for a bipartite graph, or None if not bipartite."""
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
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
                elif color[y] == color[x]:
                    return None
    return color


def _adj_from(n, E):
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    return adj


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _insert_pair(n, E, d, rng):
    """Append A-vertex u = n and B-vertex w = n + 1, each of degree d, by splitting edges.

    E lists edges as [a, b] with a on side 0 and b on side 1. Returns (n + 2, E) or None.
    """
    E = [list(e) for e in E]
    adj = _adj_from(n, E)
    adj.append(set())
    adj.append(set())
    u, w = n, n + 1
    for _ in range(d):
        for _try in range(20000):
            i = rng.randrange(len(E))
            a, b = E[i]
            if a in adj[w] or b in adj[u]:
                continue
            break
        else:
            return None
        adj[a].discard(b)
        adj[b].discard(a)
        adj[u].add(b)
        adj[b].add(u)
        adj[a].add(w)
        adj[w].add(a)
        E[i] = [u, b]
        E.append([a, w])
    return n + 2, E


def _anneal(n, E, d, D, rng, deadline):
    """Double-edge switches (degree preserving) minimizing bad pairs. Returns (success, E)."""
    E = [list(e) for e in E]
    adj = _adj_from(n, E)
    cost = _bad_pairs(n, adj, D)
    m = len(E)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    T = 0.6
    it = 0
    while cost > 0:
        it += 1
        if (it & 31) == 0:
            now = time.monotonic()
            if now > deadline:
                break
            T = 0.05 + 0.5 * max(0.0, 1.0 - (now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        adj[a1].remove(b1)
        adj[b1].remove(a1)
        adj[a2].remove(b2)
        adj[b2].remove(a2)
        adj[a1].add(b2)
        adj[b2].add(a1)
        adj[a2].add(b1)
        adj[b1].add(a2)
        new = _bad_pairs(n, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E[i] = [a1, b2]
            E[j] = [a2, b1]
            cost = new
        else:
            adj[a1].remove(b2)
            adj[b2].remove(a1)
            adj[a2].remove(b1)
            adj[b1].remove(a2)
            adj[a1].add(b1)
            adj[b1].add(a1)
            adj[a2].add(b2)
            adj[b2].add(a2)
    return cost == 0, E


# ---------------------------------------------------------------- driver

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

    best_n, best_e = base_n, base_e

    # Phase 1: Cayley-type difference-cover search.
    cay = _cayley_search(d, D, rng, start + 0.5 * total, base_n)
    if cay is not None and cay[0] > best_n and lib.is_valid(cay[0], cay[1], d, D):
        best_n, best_e = cay

    # Phase 2: grow by pairs of vertices with switch annealing.
    side = _two_color(best_n, best_e)
    if side is None:
        return best_n, best_e
    E = [[u, v] if side[u] == 0 else [v, u] for u, v in best_e]
    cur_n, cur_E = best_n, E

    while time.monotonic() < deadline:
        cand = _insert_pair(cur_n, cur_E, d, rng)
        if cand is None:
            break
        n2, E2 = cand
        ok, E3 = _anneal(n2, E2, d, D, rng, deadline)
        if not ok:
            break
        edges = [(a, b) for a, b in E3]
        if lib.is_valid(n2, edges, d, D):
            best_n, best_e = n2, edges
            cur_n, cur_E = n2, E3
        else:
            break

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return base_n, base_e
