"""Island program: group Haar graphs for D = 3 (a different construction from the voltage-lift search).

Construction: for a finite group G of order N and a set S of d elements containing the identity,
the bipartite graph with parts A = G and B = G, where a_g ~ b_{g s} for s in S, is d-regular.
It has diameter <= 3 exactly when S * S^{-1} = G (every element is a quotient of two elements of S).
Then the order is 2N, and the Moore bound for D = 3 gives N <= d^2 - d + 1.

Plan:
  1. Python builds the best known graph for (d, D) (Araujo-Lopez / projective plane), or a safe fallback.
  2. For D = 3, C searches for covering sets S in groups Z_m x| Z_k with order N = m*k,
     starting just above the start graph's half-order and going up one order at a time.
  3. C verifies its answer by BFS before printing. Python checks it again with lib.is_valid
     and keeps whichever graph is larger.
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

#define MAXG 512
#define MAXD 32
#define MAXOPT 16384

typedef struct { int m, k, r; } Opt;

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* ---------------------------------------------------------- group tables */

/* Current group Z_GM x| Z_GK with r = GR, order N; element (a,b) is a*GK+b, identity 0. */
static int N, GM, GK, GR;
static int rp[MAXG];
static int MT[MAXG][MAXG];   /* multiplication table */
static int INV[MAXG];        /* inverse table */

static void build_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x][y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x][y] == 0) { INV[x] = y; break; }
}

static Opt opts[MAXOPT];
static int nopt;

/* All groups of order n of the form Z_m x| Z_k (cyclic when r = 1). */
static void enum_opts(int n) {
    nopt = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (nopt < MAXOPT) { opts[nopt].m = 1; opts[nopt].k = k; opts[nopt].r = 0; nopt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (nopt < MAXOPT) { opts[nopt].m = m; opts[nopt].k = k; opts[nopt].r = r; nopt++; }
        }
    }
}

/* ---------------------------------------------------------- covering search */

static int S[MAXD];
static unsigned char inS[MAXG];
static unsigned int cstamp[MAXG];
static unsigned int cs_ctr = 0;
static int bestS[MAXD];

/* Number of distinct elements of S * S^{-1}. */
static int cover_count(void) {
    cs_ctr++;
    int c = 0;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            int x = MT[S[i]][INV[S[j]]];
            if (cstamp[x] != cs_ctr) { cstamp[x] = cs_ctr; c++; }
        }
    return c;
}

/* Random-restart hill climb on S (with identity fixed in S) until S S^{-1} = G. */
static int hill_climb(double until) {
    while (now() < until) {
        for (int x = 0; x < N; x++) inS[x] = 0;
        S[0] = 0;
        inS[0] = 1;
        for (int i = 1; i < d; i++) {
            int x;
            do x = rndint(N); while (inS[x]);
            S[i] = x;
            inS[x] = 1;
        }
        int cur = cover_count();
        for (long it = 0; it < 300000 && cur < N; it++) {
            if ((it & 1023) == 0 && now() > until) break;
            int i = 1 + rndint(d - 1);
            int x = rndint(N);
            if (inS[x]) continue;
            int old = S[i];
            inS[old] = 0;
            S[i] = x;
            inS[x] = 1;
            int nv = cover_count();
            if (nv >= cur || rnd01() < exp((nv - cur) / 0.5)) {
                cur = nv;
            } else {
                inS[x] = 0;
                S[i] = old;
                inS[old] = 1;
            }
        }
        if (cur == N) {
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            return 1;
        }
    }
    return 0;
}

/* ---------------------------------------------------------- output */

/* Check diameter <= 3 by BFS from a_0 and b_0 (the graph is vertex-transitive on each side). */
static int verify_set(void) {
    static int dist[2 * MAXG], q[2 * MAXG];
    for (int src = 0; src < 2; src++) {
        int s0 = src == 0 ? 0 : N;
        for (int v = 0; v < 2 * N; v++) dist[v] = -1;
        int h = 0, t = 0;
        dist[s0] = 0;
        q[t++] = s0;
        while (h < t) {
            int v = q[h++];
            if (dist[v] >= 3) continue;
            for (int i = 0; i < d; i++) {
                int u = v < N ? N + MT[v][S[i]] : MT[v - N][INV[S[i]]];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; q[t++] = u; }
            }
        }
        for (int v = 0; v < 2 * N; v++)
            if (dist[v] < 0) return 0;
    }
    return 1;
}

static void print_best(Opt o, const int *bs) {
    build_group(o.m, o.k, o.r);
    memcpy(S, bs, sizeof(int) * (size_t)d);
    if (!verify_set()) { printf("0 0\n"); return; }
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + MT[g][S[i]]);
}

/* ---------------------------------------------------------- main */

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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) { sn = 0; sm = 0; }
    for (int e = 0; e < sm; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
    }

    if (D != 3 || d < 3 || d > MAXD) { printf("0 0\n"); return 0; }

    /* Moore bound for D = 3: 2(d^2 - d + 1) vertices, so the group order is at most d^2 - d + 1. */
    int lo = d;
    if (sn / 2 + 1 > lo) lo = sn / 2 + 1;
    int hi = d * d - d + 1;
    if (hi > MAXG - 1) hi = MAXG - 1;

    int have = 0;
    Opt bo = {0, 0, 0};
    static int bS[MAXD];

    for (int n = lo; n <= hi && now() < t_end; n++) {
        enum_opts(n);
        if (nopt == 0) break;
        double cap = now() + (t_end - now()) * 0.6;
        int ok = 0;
        while (!ok && now() < cap) {
            Opt o = opts[rndint(nopt)];
            build_group(o.m, o.k, o.r);
            double slice = now() + 3.0;
            if (slice > cap) slice = cap;
            if (hill_climb(slice)) {
                ok = 1;
                bo = o;
                memcpy(bS, bestS, sizeof(int) * (size_t)d);
            }
        }
        if (!ok) break;
        have = 1;
    }

    if (!have) { printf("0 0\n"); return 0; }
    print_best(bo, bS);
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


def _safe_fallback(d, D):
    """A graph that is always valid for these parameters: K_{d,d} if D >= 2, else an edge."""
    cands = []
    if D >= 2:
        cands.append(lib.haar_graph(d, range(d)))      # K_{d,d}
    cands.append(lib.haar_graph(1, [0]))               # K_2
    for c in cands:
        if lib.is_valid(c[0], c[1], d, D):
            return c
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else _safe_fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        best = _safe_fallback(d, D)

    # Only D = 3 has the group-covering search. Moore graphs need no search.
    if D != 3 or d < 3 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
