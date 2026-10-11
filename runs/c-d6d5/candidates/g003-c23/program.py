import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: Haar-type bipartite covers of finite groups.
#
# For a finite group G (order N, elements 0..N-1) and a connection set S of
# DEG distinct elements, the graph has vertices A_g = g and B_h = N + h, with
# A_g adjacent to B_{g*s} for s in S. Every A_g has DEG neighbours and every
# B_h has DEG neighbours (B_h adjacent to A_{h*s^-1}).
#
# Left multiplication is an automorphism, so the diameter is <= D iff BFS of
# depth D from A_e and from B_e reaches all 2N vertices. Search: pick a random
# group of the required order (semidirect product Z_m x| Z_k2), then anneal
# over S. Any valid graph with 2N > best_n is recorded and the search goes on
# to larger orders.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ITERS 20000
#define MAXDEG 32

static uint64_t rs[2];

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int DEG, DIAM;
static double TL;
static int N, M, K2, R;           /* group order N = M*K2 and parameters */
static int *Rpow, *mulT, *invT;
static int S[MAXDEG], Sinv[MAXDEG];
static int *stamp, *fr, *nx;
static int curstamp;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* (a,b)*(c,e) = (a + R^b c, b + e), element index a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static void free_group(void) {
    free(Rpow); free(mulT); free(invT); free(stamp); free(fr); free(nx);
    Rpow = NULL; mulT = NULL; invT = NULL; stamp = NULL; fr = NULL; nx = NULL;
}

static void setup_group(int m, int k2, int r) {
    M = m; K2 = k2; R = r; N = m * k2;
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    mulT = malloc(sizeof(int) * (size_t)N * (size_t)N);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            mulT[(size_t)x * N + y] = gmul(x, y);
    invT = malloc(sizeof(int) * (size_t)N);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mulT[(size_t)x * N + y] == 0) invT[x] = y;
    stamp = calloc((size_t)2 * N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)2 * N);
    nx = malloc(sizeof(int) * (size_t)2 * N);
    curstamp = 0;
}

/* Number of vertices within DIAM steps of src in the Haar cover. */
static int reach_count(int src) {
    if (curstamp >= 2000000000) {
        memset(stamp, 0, sizeof(int) * (size_t)(2 * N));
        curstamp = 0;
    }
    curstamp++;
    int *f = fr, *h = nx;
    int fsz = 1, count = 1;
    f[0] = src;
    stamp[src] = curstamp;
    for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
        int nsz = 0;
        for (int q = 0; q < fsz; q++) {
            int v = f[q];
            if (v < N) {
                const int *row = mulT + (size_t)v * N;
                for (int i = 0; i < DEG; i++) {
                    int w = N + row[S[i]];
                    if (stamp[w] != curstamp) { stamp[w] = curstamp; h[nsz++] = w; }
                }
            } else {
                const int *row = mulT + (size_t)(v - N) * N;
                for (int i = 0; i < DEG; i++) {
                    int w = row[Sinv[i]];
                    if (stamp[w] != curstamp) { stamp[w] = curstamp; h[nsz++] = w; }
                }
            }
        }
        count += nsz;
        int *tmp = f; f = h; h = tmp;
        fsz = nsz;
    }
    return count;
}

/* Number of unreached (source, vertex) pairs from the two representatives. */
static long long cost_fn(void) {
    for (int i = 0; i < DEG; i++) Sinv[i] = invT[S[i]];
    int ra = reach_count(0);
    int rb = reach_count(N);
    return (long long)(2 * N - ra) + (long long)(2 * N - rb);
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++) if (S[i] == x) return 1;
    return 0;
}

static void emit(void) {
    int m = N * DEG;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int g = 0; g < N; g++) {
        for (int i = 0; i < DEG; i++) {
            best_e[idx++] = g;
            best_e[idx++] = N + mulT[(size_t)g * N + S[i]];
        }
    }
    best_m = m;
    best_n = 2 * N;
}

static long long anneal(int iters) {
    for (int i = 0; i < DEG; i++) {
        int x;
        do { x = rnd_int(N); } while (in_S(x, i));
        S[i] = x;
    }
    long long cost = cost_fn();
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 255) == 0 && elapsed() > TL) break;
        double temp = 1.2 * (1.0 - (double)it / iters) + 0.03;
        int i = rnd_int(DEG);
        int old = S[i];
        int x;
        do { x = rnd_int(N); } while (in_S(x, DEG));
        S[i] = x;
        long long c2 = cost_fn();
        if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            S[i] = old;
        }
    }
    if (cost == 0) {
        cost_fn();  /* refresh Sinv for the accepted configuration */
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    best_n = start_n;
    best_m = 0;
    if (DEG < 1 || DIAM < 1 || DEG > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < TL) {
        int lo = best_n / 2 + 1;
        if (lo < DEG + 1) lo = DEG + 1;
        int spread = 2 + lo / 8;
        int G = lo + rnd_int(spread);

        /* Choose the quotient order k2 (2..12) with G = m * k2, m >= 2 when k2 > 1. */
        int opts[16], no = 0;
        for (int c = 1; c <= 12 && c <= G; c++)
            if (G % c == 0 && G / c >= 2) opts[no++] = c;
        if (no == 0) continue;
        int c2 = opts[rnd_int(no)];
        int m = G / c2, r = 1;
        if (c2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, c2, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) {
                c2 = 1;
                m = G;
                r = 1;
            }
        }

        setup_group(m, c2, r);
        long long c = anneal(ITERS);
        if (c == 0 && 2 * N > best_n) emit();
        free_group();
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C group-cover search for a larger graph.
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    if d > 32:
        return best

    remaining = 0.85 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
