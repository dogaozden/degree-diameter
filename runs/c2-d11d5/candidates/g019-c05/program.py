"""Combined program: C bi-Cayley lift annealer over semidirect groups Z_m x| Z_k2, with a
Python fallback search and exact constructions (projective planes, Araujo-Pardo-Lopez) for D = 3.

New in this version: the bi-Cayley annealer runs entirely in C. Left multiplication by a group
element is an automorphism of a bi-Cayley lift, so a graph has diameter <= D exactly when every
vertex lies within distance D of each of the 2k block representatives (identity elements). The
C engine therefore tracks reach bitmasks over the 2k representatives only (a few bytes per vertex),
updates darts in O(|G|) per move, and tries many (block count, group) pairs inside one process.
Every returned graph is checked with lib.is_valid; K_{d,d} is the fallback.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 4
#define MAXN 65536

static int d, D;
static uint64_t rs = 88172645463325252ULL;
static unsigned char POP[256];

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ---------- semidirect group Z_M x| Z_K2, element coded as a*K2 + b ---------- */
static int K2, M, G;
static long long POW[64];
static long long CURR_R = 1;

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long ra = ((long long)a + POW[b] * (long long)c) % M;
    return (int)ra * K2 + (b + e) % K2;
}
static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long ia = ((long long)M - (POW[nb] * (long long)a) % M) % M;
    return (int)ia * K2 + nb;
}
static void set_group(int k2, int m, long long r) {
    K2 = k2;
    M = m;
    G = m * k2;
    CURR_R = r;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        POW[b] = p;
        p = (p * r) % m;
    }
}
static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}
static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}
static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
static void sample_group(int target, int *k2o, int *mo, long long *ro) {
    int k2 = K2S[rndint(20)];
    int m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    long long r = 1 % m;
    if (k2 > 1 && m > 2) {
        for (int t = 0; t < 60; t++) {
            long long c = 2 + rndint(m - 2);
            if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                r = c;
                break;
            }
        }
    }
    *k2o = k2;
    *mo = m;
    *ro = r;
}

/* ---------- bi-Cayley lift state ----------
 * Vertex v = block*G + x. A-blocks 0..K-1, B-blocks K..2K-1.
 * Layer l matches A-block i with B-block LAY[l][i] through voltage VOLT[l][i]:
 * A_{i,g} ~ B_{p, g*s}. Each layer is a perfect matching of blocks, so degrees are d. */
static int K;
static int LAY[MAXD][MAXK], INVL[MAXD][MAXK], VOLT[MAXD][MAXK];
static int NB[MAXD][MAXN];
static uint8_t REACH[MAXN], CAND[MAXN], TA[MAXN], TB[MAXN];

static void set_dart(int l, int i) {
    int p = LAY[l][i], s = VOLT[l][i], si = ginv(s);
    int ba = i * G, bb = (K + p) * G;
    for (int x = 0; x < G; x++) {
        NB[l][ba + x] = bb + gmul(x, s);
        NB[l][bb + x] = ba + gmul(x, si);
    }
}

static void swap_layer(int l, int i1, int i2) {
    int t = LAY[l][i1];
    LAY[l][i1] = LAY[l][i2];
    LAY[l][i2] = t;
    INVL[l][LAY[l][i1]] = i1;
    INVL[l][LAY[l][i2]] = i2;
    set_dart(l, i1);
    set_dart(l, i2);
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) LAY[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = LAY[l][i];
            LAY[l][i] = LAY[l][j];
            LAY[l][j] = t;
        }
        for (int i = 0; i < K; i++) VOLT[l][i] = rndint(G);
        for (int i = 0; i < K; i++) INVL[l][LAY[l][i]] = i;
        for (int i = 0; i < K; i++) set_dart(l, i);
    }
}

/* Cost = (vertex, representative) pairs at distance > D, plus a penalty per duplicate dart.
 * Writes the final reach masks into out (size >= 2KG). */
static long eval_cost(uint8_t *out) {
    int N = 2 * K * G;
    uint8_t *cur = TA, *nxt = TB;
    for (int v = 0; v < N; v++) cur[v] = (v % G == 0) ? (uint8_t)(1u << (v / G)) : 0;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint8_t c = cur[v];
            for (int l = 0; l < d; l++) c |= cur[NB[l][v]];
            nxt[v] = c;
        }
        uint8_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long unreached = 0;
    for (int v = 0; v < N; v++) {
        unreached += 2 * K - POP[cur[v]];
        out[v] = cur[v];
    }
    long dups = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (LAY[l][i] == LAY[l2][i] && VOLT[l][i] == VOLT[l2][i]) dups++;
    return unreached + 1000 * dups;
}

/* Simulated annealing on the current block count and group. Returns 1 on a valid lift. */
static int anneal(long iters, long patience, double deadline) {
    int N = 2 * K * G;
    uint8_t full = (uint8_t)((1u << (2 * K)) - 1);
    long cost = eval_cost(REACH);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0 && now_s() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rndint(100) < 25) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swap_layer(l, i1, i2);
            long c2 = eval_cost(CAND);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(REACH, CAND, (size_t)N);
                if (cost < best) {
                    best = cost;
                    last = t;
                }
            } else {
                swap_layer(l, i1, i2);
            }
            continue;
        }

        int picked = -1;
        if (rnd01() < 0.4) {
            for (int tr = 0; tr < 30; tr++) {
                int v = rndint(N);
                if (REACH[v] != full) {
                    picked = v;
                    break;
                }
            }
        }
        int l, i;
        if (picked >= 0) {
            int blk = picked / G;
            l = rndint(d);
            if (blk < K) i = blk;
            else i = INVL[l][blk - K];
        } else {
            l = rndint(d);
            i = rndint(K);
        }
        int old = VOLT[l][i];
        int nv = rndint(G);
        if (nv == old) continue;
        VOLT[l][i] = nv;
        set_dart(l, i);
        long c2 = eval_cost(CAND);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(REACH, CAND, (size_t)N);
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            VOLT[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0 ? 1 : 0;
}

/* ---------- best-so-far storage ---------- */
static int bestK, bestK2, bestM;
static long long bestR;
static int BLAY[MAXD][MAXK], BVOLT[MAXD][MAXK];
static long bestN = 0;

static void save_best(void) {
    bestK = K;
    bestK2 = K2;
    bestM = M;
    bestR = CURR_R;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            BLAY[l][i] = LAY[l][i];
            BVOLT[l][i] = VOLT[l][i];
        }
}

static void rebuild_best(void) {
    K = bestK;
    set_group(bestK2, bestM, bestR);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            LAY[l][i] = BLAY[l][i];
            VOLT[l][i] = BVOLT[l][i];
        }
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) INVL[l][LAY[l][i]] = i;
        for (int i = 0; i < K; i++) set_dart(l, i);
    }
}

static int pick_k(const int *trials, const int *wins) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) {
            bv = v;
            bk = k;
        }
    }
    return bk;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [min_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long min_n = argc > 5 ? atol(argv[5]) : 0;
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now_s();
    double deadline = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        POP[x] = (unsigned char)c;
    }

    int trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};
    double goal = (double)min_n * 1.03 + 2.0;
    if (goal < 2.0 * d) goal = 2.0 * d;

    while (now_s() < deadline) {
        int k = pick_k(trials, wins);
        int target = (int)(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        int k2, m;
        long long r;
        sample_group(target, &k2, &m, &r);
        set_group(k2, m, r);
        K = k;
        long N = 2L * K * G;
        if (N > MAXN) {
            goal = (double)bestN * 1.01 + 1.0;
            continue;
        }
        if (N <= bestN) {
            double f = (double)bestN * 1.02;
            if (goal < f) goal = f;
            continue;
        }
        trials[k]++;
        random_state();
        int ok = anneal(30000, 6000, deadline);
        if (ok) {
            wins[k]++;
            if (N > bestN) {
                bestN = N;
                save_best();
            }
            if (goal < (double)N * 1.04) goal = (double)N * 1.04;
        } else {
            double f = (double)bestN * 1.02;
            double g = goal * 0.99;
            goal = g > f ? g : f;
        }
    }

    if (bestN == 0 || bestN <= min_n) {
        printf("0 0\n");
        return 0;
    }
    rebuild_best();
    long check = eval_cost(CAND);
    if (check != 0) {
        printf("0 0\n");
        return 0;
    }
    long edges = (long)K * G * d;
    printf("%ld %ld\n", 2L * K * G, edges);
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, NB[l][v]);
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


# ----------------------------------------------------------------------------
# Python bi-Cayley search (fallback only, used if the C engine cannot run).
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
        if k >= 2 and rng.random() < 0.25:
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


def _python_lift_search(d, D, rng, deadline, best_n):
    """Python fallback: returns the best (n, edges) found that beats best_n, or None."""
    found = None
    goal = float(best_n) * 1.05 + 2.0
    while time.monotonic() < deadline:
        k = rng.choice(_KS)
        target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            goal = max(goal, best_n * 1.02 + 1.0)
            continue
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            found = res
            best_n = res[0]
            goal = max(goal, res[0] * 1.04)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.99)
    return found


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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

    # Main search: C bi-Cayley annealer (block count and group chosen by a bandit inside C).
    c_ok = False
    budget = final - time.monotonic() - 1.0
    if budget > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n],
                             stdin_graph=None, timeout=budget + 15)
            consider(*lib.parse_graph_text(text))
            c_ok = True
        except Exception:
            c_ok = False

    # Python fallback only if the C engine could not run.
    if not c_ok and final - time.monotonic() > 3.0:
        try:
            res = _python_lift_search(d, D, rng, final, best_n)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
