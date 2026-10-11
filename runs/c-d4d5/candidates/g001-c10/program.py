"""Bi-Cayley (Haar-type) search: a different construction from the lift engine.

A group G of order N with d distinct connection elements S gives the bipartite graph
a_x ~ b_{x*s} (s in S), which is d-regular on 2N vertices. The C engine enumerates every
semidirect product Z_m x|_r Z_k of order N, and simulated annealing picks S to minimise the
number of vertex pairs farther than D apart. N grows one step at a time, so the final
answer is the largest order it reaches. If the search fails, the fallback is the best
known construction for (d, D), or K_{d,d}, and every result is checked with lib.is_valid.
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

#define MAXD 16
#define MAXN 1024
#define MAXG 512
#define MAXW (MAXN / 64)
#define MAXGROUPS 8192

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd(int a, int b) {
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

/* ------------------------------------------------------------ groups */

typedef struct { int m, k, r; } GSpec;

typedef struct {
    int m, k, r;
    int rp[MAXG]; /* rp[b] = r^b mod m */
} Grp;

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)(((long)a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static void make_group(Grp *G, GSpec s) {
    G->m = s.m;
    G->k = s.k;
    G->r = s.r;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++)
        G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
}

/* All semidirect products Z_m x|_r Z_k of order N (r = 0 for the cyclic case m = 1). */
static int enum_groups(int N, GSpec *out, int cap) {
    int c = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (c < cap) { out[c].m = 1; out[c].k = k; out[c].r = 0; c++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            if (c < cap) { out[c].m = m; out[c].k = k; out[c].r = r; c++; }
        }
    }
    return c;
}

/* ------------------------------------------------------------ graph and distances */

static int adj[MAXN][MAXD];
static int dg[MAXN];
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered vertex pairs at distance > D (0 means diameter <= D). */
static long bad_pairs(int n) {
    int W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *s = cur + (size_t)adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

/* ------------------------------------------------------------ connection-set search */

static int S[MAXD];
static int bestS[MAXD];
static GSpec bestG;
static int bestN = 0;

static int used_in(int v, int upto) {
    for (int u = 0; u < upto; u++)
        if (S[u] == v) return 1;
    return 0;
}

/* Edges a_x -- b_{x*s} for x in G and s in S. Each b_y gets exactly d neighbours. */
static void build(const Grp *G, int N) {
    int n = 2 * N;
    for (int v = 0; v < n; v++) dg[v] = 0;
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++) {
            int y = gmul(G, x, S[t]);
            adj[x][dg[x]++] = N + y;
            adj[N + y][dg[N + y]++] = x;
        }
}

/* Anneal the connection set S (d distinct elements). Returns 1 if valid, 0 if not, -1 on timeout. */
static int anneal(const Grp *G, int N, long steps) {
    int n = 2 * N;
    for (int t = 0; t < d; t++) {
        int v;
        do v = rndint(N); while (used_in(v, t));
        S[t] = v;
    }
    build(G, N);
    long cost = bad_pairs(n);
    for (long it = 0; it < steps && cost > 0; it++) {
        if ((it & 127) == 0 && now() > t_end) return -1;
        if (N <= d) break; /* S must be all of G: nothing to change */
        int t = rndint(d);
        int nv;
        do nv = rndint(N); while (used_in(nv, d));
        int old = S[t];
        S[t] = nv;
        build(G, N);
        long nc = bad_pairs(n);
        double T = 0.05 + 1.5 * (1.0 - (double)it / (double)steps);
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
        } else {
            S[t] = old;
            build(G, N);
        }
    }
    return cost == 0;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    long Nmax = moore / 2;
    if (Nmax > MAXG) Nmax = MAXG;

    static GSpec groups[MAXGROUPS];
    int N = d;
    while (N <= Nmax && now() < t_end) {
        int cnt = enum_groups(N, groups, MAXGROUPS);
        if (cnt == 0) break;
        int ok = 0;
        while (!ok && now() < t_end) {
            int gi = rndint(cnt);
            Grp G;
            make_group(&G, groups[gi]);
            int res = anneal(&G, N, 20000);
            if (res < 0) break;
            if (res == 1) {
                ok = 1;
                bestN = N;
                bestG = groups[gi];
                memcpy(bestS, S, sizeof(int) * d);
            }
        }
        if (!ok) break;
        N++;
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph and double-check it before printing. */
    Grp G;
    make_group(&G, bestG);
    memcpy(S, bestS, sizeof(int) * d);
    build(&G, bestN);
    if (bad_pairs(2 * bestN) != 0) {
        printf("0 0\n");
        return 0;
    }
    long m = (long)bestN * d;
    printf("%d %ld\n", 2 * bestN, m);
    for (int x = 0; x < bestN; x++)
        for (int t = 0; t < d; t++) {
            int y = gmul(&G, x, bestS[t]);
            printf("%d %d\n", x, bestN + y);
        }
    return 0;
}
'''


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
    # Safe fallback: K_{d,d} (valid for D >= 2) or the known construction.
    best = start if start is not None else lib.haar_graph(d, range(d))
    if best[0] >= lib.moore_bound(d, D):
        return best   # already optimal, nothing to search for

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
