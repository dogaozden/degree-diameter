"""Program: parent bi-Cayley search, then a C annealer on random d-regular bipartite graphs.

New idea (not in parent): a random simple d-regular bipartite graph on n vertices
already has diameter <= D with high probability once n is moderately large, because
balls of radius ~D/2 from the two sides intersect. The C engine starts from such a
graph and anneals with degree-preserving 2-switches, minimising the number of pairs
at distance > D. Python bisects on n, keeps the parent's graph as a valid fallback,
and accepts only graphs that pass lib.is_valid.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: random d-regular bipartite start + 2-switch annealing on bad pairs.
# Input: "n 0" on stdin (n even). Output: a valid graph on n vertices, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int d, D, n, h, W;
static int *adj;      /* n*d neighbour lists; side A = [0,h), side B = [h,n) */
static u64 *R, *Rn;   /* bitsets: n rows of W words */
static u64 rs;

static u64 rnd(void) {
    rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndi(int m) { return (int)(rnd() % (u64)m); }
static double rndf(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D. */
static long long cost(void) {
    size_t tot = (size_t)n * W;
    memset(R, 0, tot * sizeof(u64));
    for (int v = 0; v < n; v++)
        R[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < D; t++) {
        memcpy(Rn, R, tot * sizeof(u64));
        for (int v = 0; v < n; v++) {
            u64 *rv = Rn + (size_t)v * W;
            const int *av = adj + (size_t)v * d;
            for (int k = 0; k < d; k++) {
                const u64 *ru = R + (size_t)av[k] * W;
                for (int w = 0; w < W; w++) rv[w] |= ru[w];
            }
        }
        u64 *tmp = R; R = Rn; Rn = tmp;
    }
    long long ones = 0;
    for (size_t i = 0; i < tot; i++) ones += popc(R[i]);
    return ((long long)n * n - ones) / 2;
}

static int has(int a, int b) {
    const int *av = adj + (size_t)a * d;
    for (int k = 0; k < d; k++) if (av[k] == b) return 1;
    return 0;
}

static void fixslot(int b, int from, int to) {
    int *ab = adj + (size_t)b * d;
    for (int k = 0; k < d; k++) if (ab[k] == from) { ab[k] = to; return; }
}

/* Current edges (a1,b1) at slot k1 of a1 and (a2,b2) at slot k2 of a2 become
   (a1,b2) at slot k1 and (a2,b1) at slot k2. Calling it again with
   (a1,k1,b2,a2,k2,b1) undoes the move. */
static void swap_edges(int a1, int k1, int b1, int a2, int k2, int b2) {
    adj[(size_t)a1 * d + k1] = b2;
    adj[(size_t)a2 * d + k2] = b1;
    fixslot(b1, a1, a2);
    fixslot(b2, a2, a1);
}

/* Random simple d-regular bipartite graph by stub pairing with local repairs. */
static int gen_random(void) {
    int N = h * d;
    int *sb = malloc(sizeof(int) * (size_t)N);
    int *bc = malloc(sizeof(int) * (size_t)n);
    int ok = 0;
    for (int att = 0; att < 200 && !ok; att++) {
        for (int i = 0; i < N; i++) sb[i] = h + i / d;
        for (int i = N - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = sb[i]; sb[i] = sb[j]; sb[j] = t;
        }
        memset(bc, 0, sizeof(int) * (size_t)n);
        int fail = 0;
        for (int i = 0; i < N && !fail; i++) {
            int a = i / d, slot = i % d;
            int tries = 0;
            while (1) {
                int bb = sb[i];
                int dup = 0;
                for (int k = 0; k < slot; k++)
                    if (adj[(size_t)a * d + k] == bb) { dup = 1; break; }
                if (!dup) break;
                if (++tries > 300) { fail = 1; break; }
                int j = i + rndi(N - i);
                int t = sb[i]; sb[i] = sb[j]; sb[j] = t;
            }
            if (fail) break;
            int b = sb[i];
            adj[(size_t)a * d + slot] = b;
            adj[(size_t)b * d + bc[b]++] = a;
        }
        if (!fail) ok = 1;
    }
    free(sb);
    free(bc);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    if (!rs) rs = 1;
    double budget = atof(argv[4]);
    int m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    (void)m;
    if (n <= 0 || (n % 2) || d < 1 || D < 1 || n < 2 * d) {
        printf("0 0\n");
        return 0;
    }
    h = n / 2;
    W = (n + 63) / 64;
    adj = malloc(sizeof(int) * (size_t)n * d);
    R = malloc(sizeof(u64) * (size_t)n * W);
    Rn = malloc(sizeof(u64) * (size_t)n * W);
    double t0 = now();
    if (!gen_random()) {
        printf("0 0\n");
        return 0;
    }
    long long cur = cost();
    double T = 0.5;
    while (cur > 0 && now() - t0 < budget) {
        int a1 = rndi(h), k1 = rndi(d);
        int a2 = rndi(h), k2 = rndi(d);
        int b1 = adj[(size_t)a1 * d + k1];
        int b2 = adj[(size_t)a2 * d + k2];
        if (a1 == a2 || b1 == b2) continue;
        if (has(a1, b2) || has(a2, b1)) continue;
        swap_edges(a1, k1, b1, a2, k2, b2);
        long long c2 = cost();
        if (c2 <= cur || rndf() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            swap_edges(a1, k1, b2, a2, k2, b1);
        }
    }
    if (cur == 0) {
        printf("%d %d\n", n, h * d);
        for (int a = 0; a < h; a++)
            for (int k = 0; k < d; k++)
                printf("%d %d\n", a, adj[(size_t)a * d + k]);
    } else {
        printf("0 0\n");
    }
    free(adj);
    free(R);
    free(Rn);
    return 0;
}
"""


def _c_random_search(d, D, seed, n, budget):
    """Run the C annealer on a random d-regular bipartite start with n vertices.

    Returns a validated (n, edges), or None if the search failed or the output is invalid.
    """
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                         stdin_graph=(n, []), timeout=budget + 30.0)
        n2, e2 = lib.parse_graph_text(text)
    except Exception:
        return None
    if n2 != n or not e2 or not lib.is_valid(n2, e2, d, D):
        return None
    return n2, e2


def _next_even(x):
    return x + (x % 2)


# ----------------------------------------------------------------------------
# Safe baseline families.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))  # ceil, so the order is at least target
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1  # dihedral-type
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                r = None
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when representative block b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def _parent_build(d, D, seed, time_limit):
    """Parent strategy: exact constructions, bi-Cayley search, slack extension."""
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


# ----------------------------------------------------------------------------
# Entry point: parent construction first (fallback), then the C annealer
# bisects on the vertex count with the remaining time.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = _parent_build(d, D, seed, 0.3 * time_limit)
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    if d < 4 or D < 3:
        return best

    deadline = t0 + time_limit - 6.0
    lo = best[0]
    hi = None
    target = lo + max(2, lo // 12)
    rounds = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 6.0:
            break
        n_t = _next_even(target)
        if n_t <= lo:
            n_t = _next_even(lo + 1)
        if hi is not None and n_t >= hi:
            break
        slice_ = min(remaining, max(6.0, remaining * 0.5))
        c_budget = slice_ - 4.0
        if c_budget < 2.0:
            break
        res = _c_random_search(d, D, seed * 1000 + rounds + 1, n_t, c_budget)
        rounds += 1
        if res is not None:
            if res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                best = res
            lo = max(lo, n_t)
        else:
            hi = n_t
        if hi is None:
            target = int(lo * 1.04)
        else:
            if hi - lo <= 2:
                break
            target = (lo + hi) // 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
