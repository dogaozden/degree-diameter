"""Program: bi-Cayley (P = 1) lifts over metacyclic groups, swept by group order with a fast two-source cost.

Construction change from the parent (voltage lifts with a random base graph and annealed voltages):
  * Single base vertex per side. Vertices are A_x and B_y for x, y in a group G of order N, with
    A_x ~ B_{x*s} for s in a connection set S of size d. Left translations act regularly on A and on B,
    so the diameter is certified by two BFS runs, one from A_e and one from B_e.
  * Groups are metacyclic Z_m x| Z_k with r^k = 1 mod m, r != 1. Orders are swept upward from the
    reference (the record's per-side size), and for each order a short simulated anneal searches over S.
  * The largest valid order found is returned.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with lib.is_valid
and keeps the best valid graph, falling back to the known start or K_{d,d}.
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

#define MAXN 2800
#define MAXD 8
#define MAXCAND 6
#define T_HI 2.5
#define T_LO 0.15
#define SLICE 0.15

static int d, D;
static long MOORE;
static double t_end, usable;
static int N;
static uint16_t T[MAXN * MAXN];   /* T[x*N+y] = x*y in the current group */
static int INV[MAXN];
static int S[MAXD], SI[MAXD];
static unsigned char inS[MAXN];
static int stampv[2 * MAXN];
static int tick = 0;
static int qv[2 * MAXN];

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

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

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,e) = (a + r^b c, b + e). Identity is code 0. */
static int build_meta(int m, int k, int r) {
    long n = (long)m * k;
    if (n > MAXN || n < 2) return 0;
    N = (int)n;
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int aa = (a + pw[b] * c) % m;
            int bb = (b + e) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    /* Inverse of (a,b) is (-r^{-b} a, -b), with r^{-b} = r^{(k-b) mod k}. */
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        long ia = ((-(long)pw[nb] * a) % m + m) % m;
        INV[x] = (int)(ia * k + nb);
    }
    return 1;
}

/* BFS from vertex src (A_x = x, B_y = N + y); returns number of vertices within distance D. */
static int ball(int src) {
    if (++tick == 0x7fffffff) {
        memset(stampv, 0, sizeof stampv);
        tick = 1;
    }
    int head = 0, tail = 0;
    stampv[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < N) {
                const uint16_t *row = &T[(size_t)v * N];
                for (int i = 0; i < d; i++) {
                    int u = N + (int)row[S[i]];
                    if (stampv[u] != tick) { stampv[u] = tick; qv[tail++] = u; }
                }
            } else {
                int y = v - N;
                const uint16_t *row = &T[(size_t)y * N];
                for (int i = 0; i < d; i++) {
                    int u = (int)row[SI[i]];
                    if (stampv[u] != tick) { stampv[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Uncovered (source, vertex) pairs from A_e and B_e; 0 means valid. */
static long cost(void) {
    return (2L * N - ball(0)) + (2L * N - ball(N));
}

static void set_slot(int i, int g) {
    inS[S[i]] = 0;
    S[i] = g;
    inS[g] = 1;
    SI[i] = INV[g];
}

/* Simulated annealing over the connection set S; returns 1 with a valid S in place. */
static int run_sa(double until) {
    memset(inS, 0, sizeof inS);
    for (int i = 0; i < d;) {
        int g = rndint(N);
        if (inS[g]) continue;
        inS[g] = 1;
        S[i] = g;
        SI[i] = INV[g];
        i++;
    }
    long cur = cost();
    if (cur == 0) return 1;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    double temp = T_HI;
    long it = 0;
    for (;;) {
        if ((++it & 31) == 0) {
            double tm = now();
            if (tm >= until) return 0;
            double fr = (tm - start) / span;
            temp = T_HI * pow(T_LO / T_HI, fr);
        }
        int i = rndint(d);
        int g = rndint(N);
        if (inS[g]) continue;
        int old = S[i];
        set_slot(i, g);
        long c2 = cost();
        long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = c2;
            if (cur == 0) return 1;
        } else {
            set_slot(i, old);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [ref_per_side]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long ref = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { print_complete(); return 0; }

    MOORE = moore_bound();
    long cap = MOORE / 2;
    if (cap > MAXN) cap = MAXN;
    long lo = ref;
    if (lo < d) lo = d;
    if (lo < 3) lo = 3;

    int bestN = 0, bm = 0, bk = 0, br = 0;
    int bestS[MAXD];

    /* Sweep per-side group orders upward; keep the largest order that yields a valid lift. */
    for (long Nn = lo; Nn <= cap && now() < t_end; Nn++) {
        int got = 0, tried = 0;
        for (long k = 2; k <= Nn / 3 && !got && tried < MAXCAND && now() < t_end; k++) {
            if (Nn % k) continue;
            long m = Nn / k;
            if (m < 3) continue;
            for (long r = 2; r < m && !got && tried < MAXCAND && now() < t_end; r++) {
                if (gcd_l(r, m) != 1 || powmod_l(r, k, m) != 1) continue;
                tried++;
                if (!build_meta((int)m, (int)k, (int)r)) continue;
                if (N < d) continue;
                double rem = t_end - now();
                double sl = SLICE < rem ? SLICE : rem;
                if (sl <= 0.0) break;
                if (run_sa(now() + sl)) {
                    got = 1;
                    bestN = (int)Nn;
                    bm = (int)m;
                    bk = (int)k;
                    br = (int)r;
                    memcpy(bestS, S, sizeof(int) * (size_t)d);
                }
            }
        }
    }

    if (!bestN) { print_complete(); return 0; }
    if (!build_meta(bm, bk, br) || N != bestN) { print_complete(); return 0; }
    for (int i = 0; i < d; i++) {
        S[i] = bestS[i];
        SI[i] = INV[S[i]];
    }
    if (cost() != 0) { print_complete(); return 0; }

    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + (int)T[(size_t)x * N + S[i]]);
    return 0;
}
'''

REF_PER_SIDE = {(4, 9): 2485}   # record 4970 = 2 * 2485 vertices


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
            ref = REF_PER_SIDE.get((d, D), best[0] // 2)
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), ref],
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
