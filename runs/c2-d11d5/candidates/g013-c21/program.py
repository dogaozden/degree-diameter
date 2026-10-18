"""Bi-Cayley lift search (new C engine) with a Python lift search as insurance.

The C engine searches voltage lifts of k base vertices per side over semidirect
products Z_m x| Z_k2 (k up to 4). Each candidate is a bi-Cayley graph, so the diameter
check needs BFS from only 2k block representatives. Simulated annealing searches over
layer permutations and voltages, and the order goal ratchets upward on success.

Every returned graph is checked with lib.is_valid. K_{d,d}, the projective plane,
the Araujo-Lopez graph, or the generalized quadrangle are the fallbacks.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Bi-Cayley lift search.
 * Usage:  prog d D seed time_limit base_n      (stdin ignored)
 * Vertices: A_{i,g} = i*G + g (i < K), B_{j,h} = (K+j)*G + h.
 * Layer l sends A_{i,g} to B_{perm[l][i], g*volt[l][i]}, so every vertex has degree d.
 * stdout: "n m" and the edges of the best valid graph with n > base_n, or "0 0".
 */

#define MAXV 40000
#define MAXD 32
#define MAXK 4

static int d, D, K, G, GM, GK;
static int rpow[64];
static int perm[MAXD][MAXK];
static int volt[MAXD][MAXK];
static int nbr[MAXV * MAXD];
static int bestnbr[MAXV * MAXD];
static int Nv;
static int bestN = 0, bestK = 0, bestG = 0;
static int dist[MAXV], queue_[MAXV], stampv[MAXV];
static int curstamp = 0;
static uint64_t rs = 88172645463325252ULL;
static double t_end;

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

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Semidirect product Z_GM x| Z_GK: (a,b)(c,e) = (a + r^b c, b + e), element coded a*GK+b. */
static int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK, c = y / GK, e = y - c * GK;
    long t = (long)rpow[b] * c + a;
    int aa = (int)(t % GM);
    int bb = b + e;
    if (bb >= GK) bb -= GK;
    return aa * GK + bb;
}

static int sample_group(int tg) {
    static const int k2s[13] = {1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12};
    for (int att = 0; att < 300; att++) {
        int k2 = k2s[rndint(13)];
        int m = (tg + k2 - 1) / k2 + rndint(3);
        if (m < 2) m = 2;
        int r = 1;
        if (k2 > 1) {
            r = -1;
            for (int t = 0; t < 400; t++) {
                int c = 1 + rndint(m - 1);
                if (gcdi(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
            if (r < 0) continue;
        }
        if (2L * K * m * k2 > MAXV) continue;
        GM = m;
        GK = k2;
        G = m * k2;
        rpow[0] = 1 % GM;
        for (int b = 1; b < GK; b++) rpow[b] = (int)((long)rpow[b - 1] * r % GM);
        return 1;
    }
    return 0;
}

static void rebuild_layer(int l) {
    for (int i = 0; i < K; i++) {
        int j = perm[l][i], s = volt[l][i];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + gmul(g, s);
            nbr[a * d + l] = b;
            nbr[b * d + l] = a;
        }
    }
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) volt[l][i] = rndint(G);
        rebuild_layer(l);
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (perm[l][i] == perm[l2][i] && volt[l][i] == volt[l2][i]) c++;
    return c;
}

/* Sum over the 2K block representatives of the number of vertices at distance > D. */
static long unreached_cost(void) {
    long total = 0;
    for (int r0 = 0; r0 < 2 * K; r0++) {
        int src = r0 * G;
        curstamp++;
        int head = 0, tail = 0;
        stampv[src] = curstamp;
        dist[src] = 0;
        queue_[tail++] = src;
        while (head < tail) {
            int v = queue_[head++];
            if (dist[v] >= D) continue;
            for (int l = 0; l < d; l++) {
                int u = nbr[v * d + l];
                if (stampv[u] != curstamp) {
                    stampv[u] = curstamp;
                    dist[u] = dist[v] + 1;
                    queue_[tail++] = u;
                }
            }
        }
        total += Nv - tail;
    }
    return total;
}

static long eval_cost(void) {
    return unreached_cost() + 1000L * dupcount();
}

static void swapp(int l, int a, int b) {
    int t = perm[l][a];
    perm[l][a] = perm[l][b];
    perm[l][b] = t;
}

static int anneal(long maxit, long patience) {
    long cost = eval_cost();
    double c0 = (double)(cost > 0 ? cost : 1);
    long bestc = cost, last = 0;
    for (long t = 0; t < maxit && cost > 0; t++) {
        if ((t & 15) == 0 && now() > t_end) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)maxit) + 0.3;
        int l = rndint(d);
        if (K >= 2 && rnd01() < 0.3) {
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swapp(l, i1, i2);
            rebuild_layer(l);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                swapp(l, i1, i2);
                rebuild_layer(l);
            }
        } else {
            int i = rndint(K);
            int old = volt[l][i], nw = rndint(G);
            if (nw == old) continue;
            volt[l][i] = nw;
            rebuild_layer(l);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                volt[l][i] = old;
                rebuild_layer(l);
            }
        }
        if (cost < bestc) { bestc = cost; last = t; }
    }
    return cost == 0;
}

static void store_best(void) {
    memcpy(bestnbr, nbr, sizeof(int) * (size_t)Nv * d);
    bestN = Nv;
    bestK = K;
    bestG = G;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit base_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long base_n = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.97 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    long trials[MAXK + 1], wins[MAXK + 1];
    for (int c = 0; c <= MAXK; c++) { trials[c] = 0; wins[c] = 0; }
    long cur_best = base_n;
    double goal = base_n * 1.01 + 1;

    while (now() < t_end) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= MAXK; c++) {
                double s = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.05 * rnd01();
                if (s > bs) { bs = s; k = c; }
            }
        }
        K = k;
        int tg = (int)(goal / (2.0 * K)) + rndint(3);
        if (tg < 2) tg = 2;
        if (!sample_group(tg)) continue;
        Nv = 2 * K * G;
        if (Nv <= cur_best) continue;
        trials[k]++;
        random_state();
        if (anneal(4000, 1000)) {
            wins[k]++;
            store_best();
            cur_best = Nv;
            goal = Nv * 1.01 + 1;
        } else {
            double floor_goal = cur_best * 1.01 + 1;
            double down = goal * 0.995;
            goal = down > floor_goal ? down : floor_goal;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    int A = bestK * bestG;
    printf("%d %d\n", bestN, A * d);
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, bestnbr[u * d + l]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
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
# Python bi-Cayley lift search (insurance path if the C engine fails).
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
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when block representative b is within distance D."""
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


def _python_lifts(d, D, rng, best_n, deadline):
    """Bandit over base sizes k with ratcheted order goal. Returns the largest (n, edges) found or None."""
    best = None
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
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
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            best = res
            best_n = res[0]
            goal = max(goal, res[0] * 1.04)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.99)
    return best


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    # Phase 1: C bi-Cayley annealing with most of the budget.
    c_budget = max(1.0, 0.8 * total)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), best_n],
                         timeout=c_budget + 10)
        n, e = lib.parse_graph_text(text)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Phase 2: Python lift search with the remaining time (insurance).
    remaining = final - time.monotonic()
    if remaining > 2.0:
        try:
            res = _python_lifts(d, D, random.Random(seed + 7), best_n, final)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
