"""Bi-Cayley voltage search with a compiled C annealing engine.

Bi-Cayley annealer (Z_m x| Z_k2 voltage lifts over 2k base vertices) in C.
Change in this version: the C engine's restarts are iterated local search.
Each restart warm-starts from the best state found so far in the same group,
with a few random voltage perturbations (and sometimes a layer swap), instead
of always restarting from a random lift. Fresh random restarts still happen
40% of the time, so the search keeps its diversity.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 8
#define PEN 1000L

static int d, D, k, m, k2, r, G, N;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int bestL[MAXD][MAXK];
static int bestS[MAXD][MAXK];
static long gbest = -1;
static int *nbr;
static uint16_t *bufA, *bufB, *resbuf, *accreach;
static int powr[64];
static unsigned char pop16[65536];
static uint64_t RS = 88172645463325252ULL;

static uint64_t rnd64(void) {
    RS ^= RS << 13;
    RS ^= RS >> 7;
    RS ^= RS << 17;
    return RS;
}

static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* Group element x = a*k2 + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k2). */
static int gmul(int x, int y) {
    int a = x / k2, b = x % k2;
    int c = y / k2, e = y % k2;
    long long t = (long long)a + (long long)powr[b] * c;
    int aa = (int)(t % m);
    int bb = b + e;
    if (bb >= k2) bb -= k2;
    return aa * k2 + bb;
}

/* Dart (l, i): A-block i (vertices i*G+g) joins B-block layers[l][i] at g*S[l][i]. */
static void set_dart(int l, int i) {
    int j = layers[l][i], s = S[l][i];
    for (int g = 0; g < G; g++) {
        int u = i * G + g;
        int w = (k + j) * G + gmul(g, s);
        nbr[(size_t)u * d + l] = w;
        nbr[(size_t)w * d + l] = u;
    }
}

/* Record the current state as the group's best if it beats every earlier restart. */
static void save_best(long cost) {
    if (gbest < 0 || cost < gbest) {
        gbest = cost;
        memcpy(bestL, layers, sizeof(layers));
        memcpy(bestS, S, sizeof(S));
    }
}

/* Count (vertex, block) pairs at distance > D from a block representative. */
static long eval_cost(void) {
    int NB = 2 * k;
    uint16_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint16_t) * (size_t)N);
    for (int b = 0; b < NB; b++) cur[(size_t)b * G] = (uint16_t)(1u << b);
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint16_t x = cur[v];
            const int *nv = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= cur[nv[l]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint16_t *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    long unreached = 0;
    for (int v = 0; v < N; v++) unreached += NB - pop16[cur[v]];
    memcpy(resbuf, cur, sizeof(uint16_t) * (size_t)N);
    return unreached;
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (layers[l1][i] == layers[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

static int search(long iters, long patience, double tend) {
    int NB = 2 * k;
    uint16_t full = (uint16_t)((1u << NB) - 1u);

    if (gbest >= 0 && rnd01() < 0.6) {
        /* Iterated local search: perturb the best lift found so far. */
        memcpy(layers, bestL, sizeof(layers));
        memcpy(S, bestS, sizeof(S));
        int nper = 1 + (d * k) / 6;
        for (int p = 0; p < nper; p++) {
            int l = rndint(d);
            int i = rndint(k);
            S[l][i] = rndint(G);
        }
        if (k >= 2 && rnd01() < 0.5) {
            int l = rndint(d);
            int i1 = rndint(k);
            int i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int t = layers[l][i1];
            layers[l][i1] = layers[l][i2];
            layers[l][i2] = t;
        }
    } else {
        /* Fresh random lift. */
        for (int l = 0; l < d; l++) {
            for (int i = 0; i < k; i++) layers[l][i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = layers[l][i];
                layers[l][i] = layers[l][j];
                layers[l][j] = t;
            }
            for (int i = 0; i < k; i++) S[l][i] = rndint(G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(l, i);

    long cost = eval_cost() + PEN * dupcount();
    memcpy(accreach, resbuf, sizeof(uint16_t) * (size_t)N);
    save_best(cost);
    double c0 = (double)(cost > 1 ? cost : 1);
    long best = cost, last = 0;

    for (long t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && now_s() > tend) return 0;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(k);
            int i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1];
            layers[l][i1] = layers[l][i2];
            layers[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = eval_cost() + PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(accreach, resbuf, sizeof(uint16_t) * (size_t)N);
                save_best(cost);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        int l = rndint(d);
        int i = rndint(k);
        if (rnd01() < 0.4) {
            /* Defect-targeted: pick a uniformly random unreached (vertex, block) owner. */
            int nb = 0, pick = -1;
            for (int v = 0; v < N; v++) {
                if (accreach[v] != full) {
                    nb++;
                    if (rndint(nb) == 0) pick = v;
                }
            }
            if (pick >= 0) {
                int block = pick / G;
                if (block < k) {
                    i = block;
                } else {
                    int j = block - k;
                    for (int q = 0; q < k; q++)
                        if (layers[l][q] == j) { i = q; break; }
                }
            }
        }

        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i);
        long c2 = eval_cost() + PEN * dupcount();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(accreach, resbuf, sizeof(uint16_t) * (size_t)N);
            save_best(cost);
            if (cost < best) { best = cost; last = t; }
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    k = atoi(argv[3]);
    m = atoi(argv[4]);
    k2 = atoi(argv[5]);
    r = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    double tl = atof(argv[8]);
    long iters = argc > 9 ? atol(argv[9]) : 20000;
    long patience = argc > 10 ? atol(argv[10]) : 4000;

    if (d < 1 || d > MAXD || k < 1 || k > MAXK || D < 1 || m < 1 || k2 < 1 || k2 > 63) {
        printf("0 0\n");
        return 0;
    }
    if (m > 100000 || (long long)m * k2 > 200000LL) { printf("0 0\n"); return 0; }
    if (r < 0) { printf("0 0\n"); return 0; }
    r %= m;
    G = m * k2;
    N = 2 * k * G;
    powr[0] = 1 % m;
    for (int b = 1; b < k2; b++) powr[b] = (int)((long long)powr[b - 1] * r % m);
    if (((long long)powr[k2 - 1] * r) % m != (1 % m)) { printf("0 0\n"); return 0; }

    for (int x = 1; x < 65536; x++) pop16[x] = (unsigned char)(pop16[x >> 1] + (x & 1));
    nbr = malloc(sizeof(int) * (size_t)N * (size_t)d);
    bufA = malloc(sizeof(uint16_t) * (size_t)N);
    bufB = malloc(sizeof(uint16_t) * (size_t)N);
    resbuf = malloc(sizeof(uint16_t) * (size_t)N);
    accreach = malloc(sizeof(uint16_t) * (size_t)N);
    if (!nbr || !bufA || !bufB || !resbuf || !accreach) { printf("0 0\n"); return 0; }

    RS = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (RS == 0) RS = 88172645463325252ULL;
    for (int w = 0; w < 10; w++) rnd64();

    double tend = now_s() + tl;
    int found = 0;
    while (now_s() < tend) {
        if (search(iters, patience, tend)) { found = 1; break; }
    }
    if (!found) { printf("0 0\n"); return 0; }

    int A = k * G;
    printf("%d %ld\n", N, (long)A * d);
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nbr[(size_t)u * d + l]);
    return 0;
}
'''


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
                for r_ in L:
                    if p < r_:
                        covered.add((p, r_))

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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (numpy fallback).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
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
    Ts = np.ascontiguousarray(M.T)
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
    """Python simulated annealing with stagnation restarts. Returns (n, edges) or None."""
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


def _c_search(d, D, k, m, k2, r, seed, slice_s):
    """Run the C annealer on one group for about slice_s seconds. Returns (n, edges) or None."""
    out = lib.run_c(C_SOURCE, [d, D, k, m, k2, r, seed, round(slice_s, 3), 20000, 4000],
                    stdin_graph=None, timeout=slice_s + 8.0)
    n, edges = lib.parse_graph_text(out)
    if n <= 0 or not edges:
        return None
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
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

    # Main search: bandit over base sizes k, C engine per group.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    c_ok = True
    while time.monotonic() < deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best_n:
            continue
        trials[k] += 1

        if c_ok:
            remaining = deadline - time.monotonic()
            slice_s = min(remaining, max(1.5, budget / 12.0))
            if slice_s < 0.5:
                break
            try:
                res = _c_search(d, D, k, m, k2, r, rng.randrange(1 << 30), slice_s)
            except (RuntimeError, ValueError, OSError):
                c_ok = False
                continue
        else:
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)

        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
