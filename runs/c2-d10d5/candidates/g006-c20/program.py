"""Bi-Cayley lift search for bipartite graphs with degree d and diameter D.

Exact constructions (projective planes, generalized quadrangle W(q)) are used where
they apply. Otherwise a C engine searches semidirect-product bi-Cayley lifts
Z_m x| Z_k2 with K base blocks per side.

New in this version (C engine):
  * Reachability uses per-vertex bitmasks over the 2K block representatives, so a
    full distance check costs O(N * d * D) bit operations, with no big-int work.
  * Iterated local search: on stagnation the engine restores the best state found in
    the current attempt and applies a small kick (three voltage re-draws), instead of
    discarding the attempt and restarting from random. Kicks are capped per attempt.
  * Bandit over base sizes K in {1..4}, as before, with group orders chosen just
    above the current best.
Every layer is a permutation, so the result is d-regular and bipartite. Only a
cost-0 state (all distances <= D, no duplicate edges) is saved.
"""
import itertools
import time

import lib


_C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 4
#define MAXN 60000
#define PEN 1000L
#define ITERS 30000L
#define PATIENCE 5000L
#define MAXKICK 4

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double T_START, DEADLINE;
static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static double elapsed(void) { return now_sec() - T_START; }

static int DEG, DIAM;
static int K, G, N, M_, K2_;
static int PW[64];
static int layers[MAXD][MAXK], S[MAXD][MAXK];
static int bestL[MAXD][MAXK], bestS[MAXD][MAXK];
static int *nbr;
static uint32_t *rcur, *rcand, *rscr;
static int bestN = 0, bestEcnt = 0;
static int *bestE;
static unsigned char PC[256];

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int powmod(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Group Z_m x| Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static void setup_group(int m, int k2, int r) {
    M_ = m;
    K2_ = k2;
    for (int t = 0; t < k2; t++) PW[t] = powmod(r, t, m);
    G = m * k2;
}

static void sample_group(int target) {
    static const int K2S[12] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16};
    int k2 = K2S[rndint(12)];
    int m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    int r = 1;
    if (k2 == 2 && m > 2 && rnd01() < 0.3) {
        r = m - 1;
    } else if (k2 > 1 && m > 2) {
        for (int tr = 0; tr < 60; tr++) {
            int c = 2 + rndint(m - 2);
            if (gcd_i(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
        }
    }
    setup_group(m, k2, r);
}

static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_, c = y / K2_, e = y % K2_;
    int ra = (int)(((long long)a + (long long)PW[b] * c) % M_);
    return ra * K2_ + (b + e) % K2_;
}

/* Layer l: A-block i joins B-block layers[l][i] with voltage S[l][i]. */
static void setdart(int l, int i) {
    int j = layers[l][i], s = S[l][i];
    int *nb = nbr + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        int A = i * G + g;
        int B = (K + j) * G + gmul(g, s);
        nb[A] = B;
        nb[B] = A;
    }
}

static void setall(void) {
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) setdart(l, i);
}

static void randomize(void) {
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) layers[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
    }
}

static int dupcount(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < DEG; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) { dup++; break; }
    return dup;
}

/* Bit b of out[v] is set when block representative b reaches v within DIAM steps.
   Returns the number of missing (representative, vertex) pairs. */
static long compute_cost(uint32_t *out) {
    int NB = 2 * K;
    for (int v = 0; v < N; v++) out[v] = 0;
    for (int b = 0; b < NB; b++) out[b * G] = 1u << b;
    uint32_t *cur = out, *nxt = rscr;
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < DEG; l++) x |= cur[nbr[(size_t)l * N + v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint32_t *tp = cur; cur = nxt; nxt = tp;
        if (!changed) break;
    }
    if (cur != out) memcpy(out, cur, sizeof(uint32_t) * (size_t)N);
    long cost = 0;
    for (int v = 0; v < N; v++) cost += NB - PC[out[v]];
    return cost;
}

static long evaluate(uint32_t *out) { return compute_cost(out) + PEN * (long)dupcount(); }

static int pick_bad(const uint32_t *r) {
    uint32_t full = (1u << (2 * K)) - 1u;
    int cnt = 0, pick = -1;
    for (int v = 0; v < N; v++)
        if (r[v] != full) {
            cnt++;
            if (rndint(cnt) == 0) pick = v;
        }
    return pick;
}

static void save_state(void) {
    memcpy(bestL, layers, sizeof layers);
    memcpy(bestS, S, sizeof S);
}

static void restore_state(void) {
    memcpy(layers, bestL, sizeof layers);
    memcpy(S, bestS, sizeof S);
    setall();
}

static void save_solution(void) {
    if (N <= bestN) return;
    int cnt = 0;
    for (int l = 0; l < DEG; l++)
        for (int v = 0; v < K * G; v++) {
            bestE[2 * cnt] = v;
            bestE[2 * cnt + 1] = nbr[(size_t)l * N + v];
            cnt++;
        }
    bestEcnt = cnt;
    bestN = N;
}

/* Iterated local search from a random start. Returns 1 if a valid lift was saved. */
static int anneal(void) {
    randomize();
    setall();
    long cost = evaluate(rcur);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long bestc = cost;
    save_state();
    long last = 0;
    int kicks = 0;
    for (long t = 0; t < ITERS && cost > 0; t++) {
        if ((t & 31) == 0 && elapsed() > DEADLINE) break;
        if (t - last > PATIENCE) {
            if (kicks >= MAXKICK) break;
            kicks++;
            restore_state();
            for (int q = 0; q < 3; q++) {
                int l = rndint(DEG), i = rndint(K);
                S[l][i] = rndint(G);
                setdart(l, i);
            }
            cost = evaluate(rcur);
            last = t;
            continue;
        }
        double temp = 0.02 * c0 * (1.0 - (double)t / (double)ITERS);
        if (temp < 0.5) temp = 0.5;
        long c2;
        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(DEG), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1];
            layers[l][i1] = layers[l][i2];
            layers[l][i2] = tmp;
            setdart(l, i1);
            setdart(l, i2);
            c2 = evaluate(rcand);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                uint32_t *tp = rcur; rcur = rcand; rcand = tp;
            } else {
                tmp = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = tmp;
                setdart(l, i1);
                setdart(l, i2);
            }
        } else {
            int u = (rnd01() < 0.4) ? pick_bad(rcur) : -1;
            int l, i;
            if (u >= 0) {
                int blk = u / G;
                l = rndint(DEG);
                if (blk < K) {
                    i = blk;
                } else {
                    int j = blk - K;
                    i = 0;
                    for (int ii = 0; ii < K; ii++)
                        if (layers[l][ii] == j) { i = ii; break; }
                }
            } else {
                l = rndint(DEG);
                i = rndint(K);
            }
            int ns = rndint(G);
            if (ns == S[l][i]) continue;
            int old = S[l][i];
            S[l][i] = ns;
            setdart(l, i);
            c2 = evaluate(rcand);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                uint32_t *tp = rcur; rcur = rcand; rcand = tp;
            } else {
                S[l][i] = old;
                setdart(l, i);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            last = t;
            save_state();
        }
    }
    if (cost == 0) {
        save_solution();
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    rs += 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    for (int b = 0; b < 256; b++) {
        int c = 0, x = b;
        while (x) { c += x & 1; x >>= 1; }
        PC[b] = (unsigned char)c;
    }
    T_START = now_sec();
    DEADLINE = tl;
    if (DEG < 2 || DEG > MAXD || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    nbr = malloc(sizeof(int) * (size_t)MAXD * MAXN);
    rcur = malloc(sizeof(uint32_t) * MAXN);
    rcand = malloc(sizeof(uint32_t) * MAXN);
    rscr = malloc(sizeof(uint32_t) * MAXN);
    bestE = malloc(sizeof(int) * 2 * (size_t)MAXN * MAXD);

    /* Safe start: K_{d,d} (diameter 2). */
    bestN = 2 * DEG;
    bestEcnt = 0;
    for (int a = 0; a < DEG; a++)
        for (int b = 0; b < DEG; b++) {
            bestE[2 * bestEcnt] = a;
            bestE[2 * bestEcnt + 1] = DEG + b;
            bestEcnt++;
        }

    int trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) { trials[k] = 0; wins[k] = 0; }

    while (elapsed() < DEADLINE) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (v > bv) { bv = v; k = kk; }
            }
        }
        K = k;
        int base = bestN / (2 * K);
        int spread = base / 8 + 1;
        int target = base + 1 + rndint(spread + 1);
        if (target < 2) target = 2;
        sample_group(target);
        N = 2 * K * G;
        if (N <= bestN || N > MAXN) continue;
        trials[k]++;
        if (anneal()) wins[k]++;
    }

    printf("%d %d\n", bestN, bestEcnt);
    for (int e = 0; e < bestEcnt; e++)
        printf("%d %d\n", bestE[2 * e], bestE[2 * e + 1]);
    return 0;
}
"""


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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

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

    # Exact constructions: return immediately for calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Search budget: leave a margin for compilation and output.
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    left = budget - (time.monotonic() - start)
    if 2 <= d <= 16 and D >= 2 and left > 1.0:
        try:
            out = lib.run_c(_C_SOURCE, [d, D, seed, round(left, 2)],
                            stdin_graph=None, timeout=left + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
