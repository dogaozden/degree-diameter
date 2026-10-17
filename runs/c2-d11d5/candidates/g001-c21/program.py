"""Bi-Cayley voltage-lift search for bipartite degree-diameter graphs.

Python handles exact constructions (projective planes, Araujo-Pardo-Lopez) and glue.
The C engine searches bi-Cayley lifts over semidirect products Z_m x| Z_k2 with
simulated annealing on layer permutations and voltages, using only K <= 4 block
representatives per side for distance checks. Each layer is a perfect matching, so
every vertex gets degree d exactly. The engine raises the order by sampling groups
slightly above the best order found so far.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 16384
#define MAXL 32
#define MAXK 4
#define PEN 1000L

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
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

/* ---------------------------------------------------------------- group Z_m x|_r Z_k2
 * Element x = a*k2 + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k2). */

static int gm, gk2, gr, Gord, K, NV;
static int rp[MAXV];

static void set_group(int m, int k2, int r) {
    gm = m; gk2 = k2; gr = r; Gord = m * k2;
    rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    return (int)(((long)a + (long)rp[b] * c) % gm) * gk2 + (b + e) % gk2;
}

/* (a,b)^{-1} = (-r^{-b} a, -b) */
static inline int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    long t = ((long)rp[nb] * a) % gm;
    int c = (int)((gm - t) % gm);
    return c * gk2 + nb;
}

/* Uniform over all (m, k2, r) with m*k2 = N, gcd(r,m)=1, r^k2 = 1 mod m. */
static int pick_group(int N, int *om, int *ok, int *orr) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k2 = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { *om = m; *ok = k2; *orr = r; }
        }
    }
    return count > 0;
}

/* ---------------------------------------------------------------- lift state */

static int layer[MAXL][MAXK];          /* layer[l][i] = B-block of A-block i in layer l */
static int S[MAXL][MAXK];              /* voltage of dart (l,i) */
static int Sinv[MAXL][MAXK];
static int nbr[MAXL][MAXV];            /* nbr[l][v] = neighbour of v in layer l */

static uint8_t bufA[MAXV], bufB[MAXV], curR[MAXV], newR[MAXV];

/* A-block i element x <-> B-block j element h: A_x ~ B_{x s}. */
static void set_dart(int l, int i) {
    int j = layer[l][i], s = S[l][i], si = Sinv[l][i];
    int Ab = i * Gord, Bb = (K + j) * Gord;
    for (int x = 0; x < Gord; x++) {
        nbr[l][Ab + x] = Bb + gmul(x, s);
        nbr[l][Bb + x] = Ab + gmul(x, si);
    }
}

/* Bit b of res[v] is set when block representative b (vertex b*Gord) is within D of v. */
static void reach_eval(uint8_t *res) {
    uint8_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, (size_t)NV);
    for (int b = 0; b < 2 * K; b++) cur[b * Gord] = (uint8_t)(1u << b);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            uint8_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint8_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    memcpy(res, cur, (size_t)NV);
}

static long unreached(const uint8_t *res) {
    long s = 0;
    for (int v = 0; v < NV; v++) s += __builtin_popcount(res[v]);
    return 2L * K * NV - s;
}

/* Count pairs of darts with the same (i, j, voltage): these would be duplicate edges. */
static long dupcount(void) {
    long c = 0;
    int T = d * K;
    for (int a = 0; a < T; a++)
        for (int b = 0; b < a; b++) {
            int la = a / K, ia = a % K, lb = b / K, ib = b % K;
            if (ia == ib && layer[la][ia] == layer[lb][ib] && S[la][ia] == S[lb][ib]) c++;
        }
    return c;
}

static long eval_cost(uint8_t *res) {
    reach_eval(res);
    return unreached(res) + PEN * dupcount();
}

/* Simulated annealing from a random start. Returns 1 when a valid lift is in state. */
static int anneal(int iters, int patience, double deadline) {
    int full = (1 << (2 * K)) - 1;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            layer[l][i] = perm[i];
            S[l][i] = rndint(Gord);
            Sinv[l][i] = ginv(S[l][i]);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);

    long cost = eval_cost(curR);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost;
    int last = 0;

    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            /* layer-swap move: exchange the B-targets of two A-blocks in one layer */
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = layer[l][i1]; layer[l][i1] = layer[l][i2]; layer[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = eval_cost(newR);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(curR, newR, (size_t)NV);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = layer[l][i1]; layer[l][i1] = layer[l][i2]; layer[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        /* voltage move: defect-targeted with probability 0.4, otherwise uniform */
        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int v = -1;
            for (int tries = 0; tries < 64; tries++) {
                int u = rndint(NV);
                if (curR[u] != full) { v = u; break; }
            }
            if (v >= 0) {
                int blk = v / Gord;
                l = rndint(d);
                if (blk < K) i = blk;
                else {
                    int j = blk - K;
                    for (int ii = 0; ii < K; ii++)
                        if (layer[l][ii] == j) { i = ii; break; }
                }
            }
        }
        if (i < 0) { l = rndint(d); i = rndint(K); }

        int old = S[l][i];
        int nw = rndint(Gord);
        if (nw == old) continue;
        S[l][i] = nw;
        Sinv[l][i] = ginv(nw);
        set_dart(l, i);
        long c2 = eval_cost(newR);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(curR, newR, (size_t)NV);
            if (cost < best) { best = cost; last = t; }
        } else {
            S[l][i] = old;
            Sinv[l][i] = ginv(old);
            set_dart(l, i);
        }
    }
    return cost == 0;
}

/* ---------------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [baseline_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long baseline = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    if (t_end < t0 + 0.1) t_end = t0 + 0.1;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXL || D < 2) { printf("0 0\n"); return 0; }

    long best_n = baseline;
    int found = 0;
    int bestK = 0, bestM = 0, bestK2 = 0, bestR = 0;
    static int bestLayer[MAXL][MAXK], bestS[MAXL][MAXK];
    int trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};

    while (now() < t_end) {
        int k;
        if (rnd01() < 0.2) k = 1 + rndint(MAXK);
        else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (v > bv) { bv = v; k = kk; }
            }
        }
        long Gmin = best_n / (2L * k) + 1;
        if (2L * Gmin > MAXV) break;
        if (2L * k * Gmin > MAXV) continue;
        long span = Gmin / 8 + 2;
        long Gt = Gmin + rndint((int)span);
        if (2L * k * Gt > MAXV) Gt = Gmin;

        int m2, k2, r2;
        if (!pick_group((int)Gt, &m2, &k2, &r2)) continue;
        set_group(m2, k2, r2);
        K = k;
        NV = 2 * K * Gord;
        trials[k]++;
        int ok = anneal(20000, 4000, t_end);
        if (ok && NV > best_n) {
            wins[k]++;
            best_n = NV;
            found = 1;
            bestK = K; bestM = m2; bestK2 = k2; bestR = r2;
            memcpy(bestLayer, layer, sizeof layer);
            memcpy(bestS, S, sizeof S);
        }
    }

    if (!found) { printf("0 0\n"); return 0; }

    K = bestK;
    set_group(bestM, bestK2, bestR);
    NV = 2 * K * Gord;
    memcpy(layer, bestLayer, sizeof layer);
    memcpy(S, bestS, sizeof S);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            Sinv[l][i] = ginv(S[l][i]);
            set_dart(l, i);
        }
    long m = (long)K * Gord * d;
    printf("%d %ld\n", NV, m);
    for (int v = 0; v < K * Gord; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nbr[l][v]);
    return 0;
}
'''


def known_start(d, D):
    """Exact or record construction Python can build directly, or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    start = known_start(d, D)
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing can beat it

    budget = min(0.85 * time_limit, time_limit - 6.0) - (time.monotonic() - t0)
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
        except (RuntimeError, ValueError):
            out = None
        if out is not None and out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
