"""Program: bi-Cayley (single-base) lifts over metacyclic groups, found by cheap random connection-set search.

This replaces the previous annealed voltage-lift engine with a different construction:

  * Graph: vertices A(x), B(y) for x, y in a group G of order N. Edges A(x)--B(x*s) for s in a
    connection set S = {s_1..s_d} of distinct elements. Left multiplication by G is an
    automorphism acting transitively on A and on B, so the diameter is <= D iff BFS from
    A(e) and from B(e) reaches all 2N vertices within D steps. Each trial costs two BFS runs.
  * WLOG s_1 = e (right multiplication by s_1^{-1} relabels S), so only d-1 elements are sampled.
  * Groups: metacyclic Z_m x| Z_k (r^k = 1 mod m, gcd(r,m) = 1; r = 1 gives abelian groups),
    with 2N in a window just below the target record. The engine keeps the largest N that
    succeeded, and only samples candidate groups with larger N (biased toward the threshold).
  * Groups are multiplied in closed form, so no multiplication table is stored.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks any output with
lib.is_valid and keeps the best valid graph, falling back to the known start or K_{d,d}.
Note: this version has not been executed in this session, so its speed and success rate are
unverified. The validity checks in Python keep it safe even if the search underperforms.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 8
#define NHI_CAP 4000
#define MAXV (2 * NHI_CAP)
#define MAXCAND 400000
#define BATCH 64
#define SLACK 600

typedef struct { int m, k, r, N; } Cand;

static Cand CAND[MAXCAND];
static int nc = 0;

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------ group Z_m x| Z_k */

static int M = 2, K = 1, NN = 2, RR = 1;
static int PW[NHI_CAP];   /* PW[b] = r^b mod m */

static void set_group(int m, int k, int r) {
    M = m;
    K = k;
    RR = r;
    NN = m * k;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (int)((long)PW[b - 1] * r % m);
}

/* Element (a,b) coded as a*K+b; (a,b)(c,e) = (a + r^b c, b + e). */
static inline int gmul(int x, int y) {
    int a = x / K, b = x - a * K;
    int c = y / K, e = y - c * K;
    int aa = (a + PW[b] * c) % M;
    int bb = b + e;
    if (bb >= K) bb -= K;
    return aa * K + bb;
}

/* Inverse of (a,b) is (-r^{-b} a, -b). */
static inline int ginv(int x) {
    int a = x / K, b = x - a * K;
    int nb = (K - b) % K;
    int na = (M - (int)((long)PW[nb] * a % M)) % M;
    return na * K + nb;
}

static void gen_cands(long lo, long hi) {
    nc = 0;
    for (long N = lo; N <= hi; N++) {
        for (long k = 1; k <= N / 2; k++) {
            if (N % k) continue;
            long m = N / k;
            if (m < 2) continue;
            for (long r = 1; r < m; r++) {
                if (k == 1 && r != 1) break;   /* cyclic Z_N: only r = 1 */
                if (powmod_l(r, k, m) != 1 % m) continue;
                if (gcd_l(r, m) != 1) continue;
                if (nc >= MAXCAND) return;
                CAND[nc].m = (int)m;
                CAND[nc].k = (int)k;
                CAND[nc].r = (int)r;
                CAND[nc].N = (int)N;
                nc++;
            }
        }
    }
}

/* ------------------------------------------------------------ BFS check */

static int SG[MAXD], SI[MAXD];
static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* True iff BFS from src reaches all 2*NN vertices within Dl steps. */
static int reach_all(int src, int Dl) {
    int total = 2 * NN;
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < Dl && head < tail && tail < total; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < NN) {
                for (int j = 0; j < d; j++) {
                    int u = NN + gmul(v, SG[j]);
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int y = v - NN;
                for (int j = 0; j < d; j++) {
                    int u = gmul(y, SI[j]);
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail == total;
}

/* ------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static long moore_bound(void) {
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [ref_vertices]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long ref = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    double usable = limit - 2.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long lo = ref > 0 ? ref / 2 - SLACK : 2;
    if (lo < d) lo = d;
    if (lo < 2) lo = 2;
    long hi = NHI_CAP;
    if (2 * hi > moore) hi = moore / 2;
    if (hi < lo) { print_complete(); return 0; }
    gen_cands(lo, hi);

    int bestN = 0, first = 0;
    int bM = 0, bK = 0, bR = 0;
    int bestS[MAXD];
    int bestSet = 0;

    while (nc > 0) {
        if (now() >= t_end) break;
        while (first < nc && CAND[first].N <= bestN) first++;
        if (first >= nc) break;

        /* Bias toward the candidates just above the current best order. */
        int span = nc - first;
        double u = rnd01();
        int idx = first + (int)(u * u * u * span);
        if (idx >= nc) idx = nc - 1;
        set_group(CAND[idx].m, CAND[idx].k, CAND[idx].r);

        for (int bt = 0; bt < BATCH; bt++) {
            if (now() >= t_end) break;
            SG[0] = 0;
            for (int j = 1; j < d; j++) {
                int x, dup;
                do {
                    x = 1 + rndint(NN - 1);
                    dup = 0;
                    for (int t = 0; t < j; t++)
                        if (SG[t] == x) { dup = 1; break; }
                } while (dup);
                SG[j] = x;
            }
            for (int j = 0; j < d; j++) SI[j] = ginv(SG[j]);
            if (!reach_all(0, D)) continue;       /* from A(e) */
            if (!reach_all(NN, D)) continue;      /* from B(e) */
            bestN = NN;
            bM = M;
            bK = K;
            bR = RR;
            memcpy(bestS, SG, sizeof(int) * (size_t)d);
            bestSet = 1;
            break;
        }
    }

    if (!bestSet) { print_complete(); return 0; }
    set_group(bM, bK, bR);
    printf("%d %d\n", 2 * NN, NN * d);
    for (int x = 0; x < NN; x++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", x, NN + gmul(x, bestS[j]));
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), best[0])
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), ref],
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
