"""Bold revision: a cyclic / bi-Cayley voltage search in C replaces the grow-by-two engine.

Pipeline (all results checked with lib.is_valid; K_{d,d} or an exact construction is the fallback):
  1. Exact constructions where they exist (projective planes, Araujo-Lopez, W(q) for D = 4).
  2. A short Python semidirect-product lift search, as a baseline that is guaranteed to return something.
  3. C annealing over bi-Cayley graphs on k blocks per side over Z_m (k = 1, 2, 3). Each block
     pair (i, j) carries a shift set; A_{i,x} ~ B_{j,x+s}. The graph is d-regular by construction.
     Because of translation symmetry, diameter is checked by BFS from one representative per block.
     The order 2km is ratcheted by bisection, with simulated annealing on the shifts at each order.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
/* Bi-Cayley annealing over Z_m with K blocks per side.
 * Usage: prog d D seed time_limit K mstart
 * Output: "n m" + edges of the largest valid graph found, or "0 0".
 * Vertices: A_{i,x} = i*m + x, B_{j,x} = (K+j)*m + x.
 * Edges: A_{i,x} ~ B_{j,(x+s)%m} for s in S[i][j], |S[i][j]| = c[(j-i) mod K], sum c = d.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 4
#define MAXD 32
#define MAXM 40000
#define MAXV (2 * MAXK * MAXM)
#define ITER 40000

static int d, D, K;
static int cpat[MAXK];
static int S[MAXK][MAXK][MAXD];
static int bestS[MAXK][MAXK][MAXD];
static int bestc[MAXK];
static int bestK = 0, bestm = 0;
static uint64_t rs = 88172645463325252ULL;
static int vis[MAXV];
static int vstamp = 0;
static int qbuf[MAXV];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Number of vertices within distance D of src (src included). */
static int reach_count(int src, int m) {
    if (vstamp >= 2000000000) {
        memset(vis, 0, sizeof(vis));
        vstamp = 0;
    }
    vstamp++;
    int head = 0, tail = 0;
    qbuf[tail++] = src;
    vis[src] = vstamp;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = qbuf[head++];
            if (v < K * m) {
                int i = v / m, x = v - i * m;
                for (int j = 0; j < K; j++) {
                    int t = (j - i + K) % K;
                    for (int q = 0; q < cpat[t]; q++) {
                        int w = (K + j) * m + (x + S[i][j][q]) % m;
                        if (vis[w] != vstamp) {
                            vis[w] = vstamp;
                            qbuf[tail++] = w;
                        }
                    }
                }
            } else {
                int j = v / m - K, y = v - (K + j) * m;
                for (int i = 0; i < K; i++) {
                    int t = (j - i + K) % K;
                    for (int q = 0; q < cpat[t]; q++) {
                        int w = i * m + (y - S[i][j][q] + m) % m;
                        if (vis[w] != vstamp) {
                            vis[w] = vstamp;
                            qbuf[tail++] = w;
                        }
                    }
                }
            }
        }
    }
    return tail;
}

/* Sum over block representatives of the number of vertices at distance > D.
 * Translations are automorphisms, so one representative per block suffices. */
static long eval_cost(int m) {
    long c = 0;
    int N = 2 * K * m;
    for (int b = 0; b < 2 * K; b++) c += N - reach_count(b * m, m);
    return c;
}

static void random_pattern(void) {
    for (int t = 0; t < K; t++) cpat[t] = 0;
    for (int r = 0; r < d; r++) cpat[rndint(K)]++;
}

static void init_shifts(int m) {
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++) {
            int t = (j - i + K) % K;
            for (int q = 0; q < cpat[t]; q++) {
                int v, ok;
                do {
                    v = rndint(m);
                    ok = 1;
                    for (int r = 0; r < q; r++)
                        if (S[i][j][r] == v) { ok = 0; break; }
                } while (!ok);
                S[i][j][q] = v;
            }
        }
}

static void save_best(int m) {
    bestK = K;
    bestm = m;
    for (int t = 0; t < K; t++) bestc[t] = cpat[t];
    memcpy(bestS, S, sizeof(S));
}

static int anneal(int m, double until) {
    random_pattern();
    for (int t = 0; t < K; t++)
        if (cpat[t] > m) return 0;
    init_shifts(m);
    long cost = eval_cost(m);
    if (cost == 0) {
        save_best(m);
        return 1;
    }
    double T0 = 1.0 + 0.02 * (double)cost;
    for (long it = 0; it < ITER; it++) {
        if ((it & 15) == 0 && now() > until) break;
        int i = rndint(K), j = rndint(K);
        int t = (j - i + K) % K;
        if (cpat[t] == 0) continue;
        int q = rndint(cpat[t]);
        int nv = rndint(m), dup = 0;
        for (int r = 0; r < cpat[t]; r++)
            if (S[i][j][r] == nv) { dup = 1; break; }
        if (dup) continue;
        int old = S[i][j][q];
        S[i][j][q] = nv;
        long nc = eval_cost(m);
        double T = T0 * (1.0 - (double)it / ITER) + 0.05;
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
            if (cost == 0) {
                save_best(m);
                return 1;
            }
        } else {
            S[i][j][q] = old;
        }
    }
    return 0;
}

static void print_best(void) {
    if (bestm <= 0) {
        printf("0 0\n");
        return;
    }
    int m = bestm, k = bestK;
    long N = 2L * k * m, E = (long)k * m * d;
    printf("%ld %ld\n", N, E);
    for (int i = 0; i < k; i++)
        for (int x = 0; x < m; x++)
            for (int j = 0; j < k; j++) {
                int t = (j - i + k) % k;
                for (int q = 0; q < bestc[t]; q++)
                    printf("%d %d\n", i * m + x, (k + j) * m + (x + bestS[i][j][q]) % m);
            }
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed time_limit K mstart\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    long mstart = atol(argv[6]);
    if (d < 1 || d > MAXD || D < 2 || K < 1 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    double deadline = t0 + limit * 0.93 - 0.3;
    long lo = 0, hi = 0, m = mstart;
    if (m < d + 2) m = d + 2;

    while (now() < deadline && m >= d + 2 && m < MAXM) {
        double rem = deadline - now();
        double slice = rem < 4.0 ? rem : 4.0;
        int ok = anneal((int)m, now() + slice);
        if (ok) {
            lo = m;
            if (hi == 0)
                m = m + m / 40 + 1;
            else if (hi - lo > 1)
                m = (lo + hi) / 2;
            else
                m = lo + 1;
        } else {
            if (hi == 0 || m < hi) hi = m;
            if (lo == 0)
                m = m - (m * 3) / 20 - 1;
            else if (hi - lo > 1)
                m = (lo + hi) / 2;
            else
                m = lo + 1;
        }
    }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions.
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


# ----------------------------------------------------------------------------
# Python baseline: bi-Cayley lifts over semidirect products Z_m x| Z_k2.
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
    """Return (G, Ts, Invs) with Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h."""
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
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
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
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation stop. Returns (n, edges) or None."""
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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(2.0, 0.85 * time_limit - 2.0)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Phase 1: Python semidirect lift baseline, so a valid large graph exists early.
    lift_deadline = t0 + 0.2 * total
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < lift_deadline:
        k = pick_k()
        target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(float(best_n) * 1.02, goal * 0.99)
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            goal = max(goal, best_n * 1.02)
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, lift_deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])
            goal = max(goal, res[0] * 1.04)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.99)

    # Phase 2: C bi-Cayley annealing with bisection on the group order, for k = 1, 2, 3.
    moore = lib.moore_bound(d, D)
    runs = [1, 2, 3]
    for idx, k in enumerate(runs):
        remaining = final - time.monotonic()
        if remaining < 3.0:
            break
        share = remaining / (len(runs) - idx)
        mstart = max(d + 2, int(max(0.25 * moore, best_n) / (2 * k)))
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed + idx, round(share, 2), k, mstart],
                             stdin_graph=None, timeout=share + 10)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
