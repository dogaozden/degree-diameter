"""Bold variant for the d6D5 target: non-Haar voltage lifts of small bipartite base graphs over non-abelian
groups (Z_m x| Z_k), searched by annealing with an exact cost.

CONSTRUCTION.  Take a bipartite base multigraph with p vertices on each side and degree DEG (its incidence
matrix is a sum of DEG permutation matrices).  Assign each dart (a, b) a voltage g in G (distinct within a
parallel class, so no duplicate edges).  The lift has vertices (u, x), u in base, x in G, and edges
(a, x) ~ (p+b, x*g).  Left multiplication by h in G is an automorphism, so the diameter is exactly the maximum
eccentricity over the 2p representatives (u, e).  The cost is the number of vertices missed within distance
DIAM from these representatives, so cost 0 means a valid graph.  The order is 2*p*|G| (> 684 for the configs
below).

SAFETY.  Every returned graph passes lib.is_valid.  If the search finds nothing, the parent's valid 660-vertex
Haar graph is returned, and for other cases a small always-valid graph.
"""
import math
import random
import time

import lib

TARGET = (6, 5)
DEG = 6
DIAM = 5
# (p, Mlo, Mhi): p vertices per side, group order M in [Mlo, Mhi].  Orders 2*p*M are 688..760 (> 684).
CONFIGS = [(2, 172, 190), (3, 115, 127)]
# Valid Haar graph Z_33 x| Z_10 (lam = 26), S of six elements: 660 vertices.
FALLBACK_HAAR = (33, 10, 26, [0, 179, 116, 180, 47, 306])


# ------------------------------------------------------------------------------ small safe graphs

def _small(d, D):
    """Always-valid small graph for any other (d, D); the last resort is one isolated vertex."""
    cands = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        cands.append(lambda: lib.projective_plane_incidence(d - 1))
    if D == 3 and 3 <= d - 2 <= 30 and lib.is_prime_power(d - 2):
        cands.append(lambda: lib.araujo_lopez_graph(d - 2))
    cands.append(lambda: lib.haar_graph(d, range(d)))
    for make in cands:
        try:
            n, e = make()
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            pass
    return 1, []


def _haar_fallback(d, D):
    """The parent's valid Haar graph (660 vertices for d=6, D=5), re-checked before return."""
    m, k, lam, S = FALLBACK_HAAR
    N, mul, _ = lib.semidirect_group(m, k, lam)
    edges = [(g, N + mul(s, g)) for s in S for g in range(N)]
    n = 2 * N
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


# ------------------------------------------------------------------------------ group helpers

def _groups(M):
    """Non-abelian semidirect products Z_m x| Z_k of order M, as (m, k, r) triples with r != 1."""
    out = []
    for k in range(2, M):
        if M % k:
            continue
        m = M // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Multiplication table MT[x][g] = x*g (identity is element 0)."""
    N, mul, _ = lib.semidirect_group(m, k, r)
    return N, [[mul(x, g) for g in range(N)] for x in range(N)]


# ------------------------------------------------------------------------------ lift and cost

def _random_mat(p, rng):
    """p x p nonnegative integer matrix with all row and column sums DEG (sum of DEG permutation matrices)."""
    mat = [[0] * p for _ in range(p)]
    for _ in range(DEG):
        perm = list(range(p))
        rng.shuffle(perm)
        for a in range(p):
            mat[a][perm[a]] += 1
    return mat


def _adj(p, M, MT, darts):
    """Adjacency lists of the lift.  A-vertex (a, x) is a*M + x, B-vertex (b, y) is (p+b)*M + y."""
    adj = [[] for _ in range(2 * p * M)]
    for a, b, g in darts:
        base_b = (p + b) * M
        for x in range(M):
            u = a * M + x
            v = base_b + MT[x][g]
            adj[u].append(v)
            adj[v].append(u)
    return adj


def _missing(adj, n, src):
    """Number of vertices NOT within DIAM steps of src."""
    seen = bytearray(n)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(DIAM):
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
    return n - cnt


def _cost(p, M, adj):
    """Total misses from the 2p representatives (u, e).  Zero iff the lift has diameter <= DIAM."""
    n = 2 * p * M
    reps = [a * M for a in range(p)] + [(p + b) * M for b in range(p)]
    return sum(_missing(adj, n, s) for s in reps)


def _lift_edges(p, M, MT, darts):
    edges = []
    for a, b, g in darts:
        base_b = (p + b) * M
        for x in range(M):
            edges.append((a * M + x, base_b + MT[x][g]))
    return 2 * p * M, edges


# ------------------------------------------------------------------------------ annealing

def _init_voltages(pairs, M, rng):
    V = [0] * len(pairs)
    for pr in set(pairs):
        idx = [i for i, q in enumerate(pairs) if q == pr]
        for i, v in zip(idx, rng.sample(range(M), len(idx))):
            V[i] = v
    return V


def _anneal(p, M, MT, mat, rng, t_end):
    """Anneal the dart voltages for one base matrix.  Returns the darts [(a, b, g)] of a cost-0 lift, or None."""
    pairs = []
    for a in range(p):
        for b in range(p):
            pairs += [(a, b)] * mat[a][b]
    nd = len(pairs)
    sib = {i: [j for j, q in enumerate(pairs) if q == pairs[i] and j != i] for i in range(nd)}
    V = _init_voltages(pairs, M, rng)

    def darts():
        return [(pairs[i][0], pairs[i][1], V[i]) for i in range(nd)]

    def evaluate():
        return _cost(p, M, _adj(p, M, MT, darts()))

    cur = evaluate()
    best, since, T = cur, 0, 0.7
    while True:
        if cur == 0:
            return darts()
        if time.monotonic() >= t_end:
            return None
        if since > 1500:  # stuck: restart from fresh voltages
            V = _init_voltages(pairs, M, rng)
            cur = evaluate()
            best, since = cur, 0
            continue
        i = rng.randrange(nd)
        used = {V[j] for j in sib[i]}
        choices = [g for g in range(M) if g not in used and g != V[i]]
        if not choices:
            continue
        old = V[i]
        V[i] = rng.choice(choices)
        new = evaluate()
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            if cur < best:
                best, since = cur, 0
            else:
                since += 1
        else:
            V[i] = old
            since += 1


# ------------------------------------------------------------------------------ search driver

def _search(seed, t_end, slice_len):
    rng = random.Random(seed)
    group_cache = {}
    groups_by_M = {}
    attempt = 0
    while time.monotonic() < t_end:
        p, lo, hi = CONFIGS[attempt % len(CONFIGS)]
        attempt += 1
        M = rng.randint(lo, hi)
        if M not in groups_by_M:
            groups_by_M[M] = _groups(M)
        gl = groups_by_M[M]
        if not gl:
            continue
        key = rng.choice(gl)
        if key not in group_cache:
            group_cache[key] = _table(*key)
        N, MT = group_cache[key]
        mat = _random_mat(p, rng)
        end = min(t_end, time.monotonic() + slice_len)
        darts = _anneal(p, N, MT, mat, rng, end)
        if darts is not None:
            n, edges = _lift_edges(p, N, MT, darts)
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


# ------------------------------------------------------------------------------ entry point

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if (d, D) == TARGET:
        budget = 0.70 * time_limit
        try:
            res = _search(seed, t0 + budget, max(4.0, 0.25 * budget))
            if res is not None:
                return res
        except Exception:
            pass
        try:
            res = _haar_fallback(d, D)
            if res is not None:
                return res
        except Exception:
            pass
    return _small(d, D)
