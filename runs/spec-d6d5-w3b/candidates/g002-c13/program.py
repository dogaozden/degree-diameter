import math
import random
import time

import lib


class _Group:
    """Finite group given by multiplication and inversion on indices 0..order-1 (identity 0)."""

    def __init__(self, order, mul, inv):
        self.G = order
        self._mul = mul
        self._inv = inv
        self._cache = {}

    def perm(self, s):
        """Right-multiplication table a -> a*s, cached per s."""
        r = self._cache.get(s)
        if r is None:
            mul = self._mul
            r = [mul(a, s) for a in range(self.G)]
            self._cache[s] = r
        return r

    def inv(self, s):
        return self._inv(s)


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k with m*k = G (k = 1 gives cyclic)."""
    divs = [k for k in range(1, G + 1) if G % k == 0]
    for _ in range(40):
        k = rng.choice(divs)
        m = G // k
        if m == 1:
            r = 0
        else:
            cands = [x for x in range(1, m)
                     if math.gcd(x, m) == 1 and pow(x, k, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        return _Group(order, mul, inv)
    return None


def _bi_cost(grp, D, S):
    """Bi-Cayley graph on A = G, B = G with a ~ b iff a^{-1} b in S.

    The graph is vertex-transitive on each side, so BFS from the identity of
    A and of B covers all pairs. Returns the number of (source, vertex) pairs
    not reached within distance D; zero means diameter <= D.
    """
    G = grp.G
    inv = grp.inv
    Rs = [grp.perm(s) for s in S]
    Ri = [grp.perm(inv(s)) for s in S]
    N = 2 * G
    adj = [None] * N
    for a in range(G):
        adj[a] = [G + r[a] for r in Rs]
    for b in range(G):
        adj[G + b] = [r[b] for r in Ri]
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _search_S(grp, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets S of size d in the group."""
    G = grp.G
    if G < d:
        return None
    S = rng.sample(range(G), d)
    cost = _bi_cost(grp, D, S)
    T = 2.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T2 = list(S)
        T2[i] = x
        c2 = _bi_cost(grp, D, T2)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S, cost = T2, c2
        T = max(0.05, T * 0.998)
    return S if cost == 0 else None


def _graph(grp, S):
    """Edges of the bi-Cayley graph: (a, G + a*s) for every a and s in S."""
    G = grp.G
    rs = [grp.perm(s) for s in S]
    edges = []
    for a in range(G):
        for r in rs:
            edges.append((a, G + r[a]))
    return 2 * G, edges


def _bicayley_search(d, D, rng, deadline, current_G, consider):
    """Climb the bi-Cayley order G one step at a time, keeping valid graphs."""
    iters = 1200 if D >= 5 else 500
    while time.monotonic() < deadline:
        lo = current_G() + 1
        width = max(1, lo // 80)
        G = rng.randint(lo, lo + width)
        grp = _sample_group(G, rng)
        if grp is None:
            continue
        S = _search_S(grp, d, D, rng, deadline, iters)
        if S is None:
            continue
        n, e = _graph(grp, S)
        consider(n, e)


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_candidate(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.80 * time_limit)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
            return True
        return False

    rng = random.Random(seed)

    try:
        if D == 3:
            pg = _pg_candidate(d)
            if pg is not None:
                consider(pg[0], pg[1])
            ar = _araujo_candidate(d)
            if ar is not None:
                consider(ar[0], ar[1])

        if D >= 3:
            _bicayley_search(d, D, rng, deadline,
                             lambda: best_n // 2, consider)
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
