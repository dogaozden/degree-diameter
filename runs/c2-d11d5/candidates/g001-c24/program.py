"""Bi-Cayley (Haar-type) search: a different construction from the lift search.

Graph: A = {0..N-1}, B = {N..2N-1}, edges A_x ~ B_{x*s} for s in S, |S| = d, where G is a
group of order N (Z_m x|_r Z_k). Left translations are automorphisms, so the diameter is
<= D iff every vertex is within D of A_e and of B_e. The C engine climbs a ladder N = best+1,
annealing S until the two BFS balls cover everything. Python keeps a valid fallback.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley (Haar-type) search.
 * Vertices A = 0..N-1, B = N..2N-1. A_x ~ B_{x*s} for s in S, |S| = d, S a set of distinct
 * elements of a group G of order N, G = Z_m x|_r Z_k with element (a,b) = a*k+b.
 * Left translations are automorphisms, so diameter <= D iff every vertex is within D of
 * A_e and of B_e. Simulated annealing over S minimises the number of unreached vertices.
 * Ladder: N grows by one each time an annealing attempt succeeds.
 * Usage: prog d D seed time_limit   (stdin ignored). stdout: "n m" then edges.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 8192
#define MAXDEG 32
#define MAXGROUPS 200000
#define ATTEMPT 4.0

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
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

/* ---------------------------------------------------------------- groups */

typedef struct { int m, k, r; } Grp;   /* Z_m x|_r Z_k, order m*k */
static Grp *glist = NULL;
static int gcount = 0;

static int N, gm, gk;
static int rp[MAXG];                   /* rp[b] = r^b mod m */

static void add_group(int m, int k, int r) {
    if (gcount < MAXGROUPS) {
        glist[gcount].m = m;
        glist[gcount].k = k;
        glist[gcount].r = r;
        gcount++;
    }
}

/* All semidirect groups of order Nn: m | Nn, k = Nn/m, gcd(r,m)=1, r^k = 1 mod m. */
static void enum_groups(int Nn) {
    gcount = 0;
    for (int m = 1; m <= Nn; m++) {
        if (Nn % m) continue;
        int k = Nn / m;
        if (m == 1) { add_group(1, k, 0); continue; }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            add_group(m, k, r);
        }
    }
}

static void set_group(Grp G) {
    gm = G.m;
    gk = G.k;
    N = G.m * G.k;
    rp[0] = 1 % gm;
    for (int b = 1; b < gk; b++) rp[b] = (int)((long)rp[b - 1] * G.r % gm);
}

/* (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    return (int)((((long)a + (long)rp[b] * c) % gm) * gk + (b + e) % gk);
}

/* ---------------------------------------------------------------- graph state */

static int S[MAXDEG];
static int perm[MAXDEG][MAXG];   /* perm[j][x] = x * S[j]        (A index -> B index)  */
static int invp[MAXDEG][MAXG];   /* invp[j][y] = y * S[j]^{-1}   (B index -> A index)  */
static int vis[2 * MAXG];
static int stampv = 0;
static int qbuf[2 * MAXG];

static void update_row(int j) {
    for (int x = 0; x < N; x++) {
        int y = gmul(x, S[j]);
        perm[j][x] = y;
        invp[j][y] = x;
    }
}

static void update_all(void) {
    for (int j = 0; j < d; j++) update_row(j);
}

static int in_S_n(int g, int cnt) {
    for (int i = 0; i < cnt; i++)
        if (S[i] == g) return 1;
    return 0;
}

static void random_S(void) {
    for (int j = 0; j < d; j++) {
        int g;
        do { g = rndint(N); } while (in_S_n(g, j));
        S[j] = g;
    }
    update_all();
}

/* Number of (source, vertex) pairs at distance > D, sources A_e and B_e. 0 = valid. */
static long cost(void) {
    long bad = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        stampv++;
        int qh = 0, qt = 0;
        qbuf[qt++] = s0;
        vis[s0] = stampv;
        for (int depth = 0; depth < D && qh < qt; depth++) {
            int end = qt;
            while (qh < end) {
                int v = qbuf[qh++];
                if (v < N) {
                    for (int j = 0; j < d; j++) {
                        int u = N + perm[j][v];
                        if (vis[u] != stampv) { vis[u] = stampv; qbuf[qt++] = u; }
                    }
                } else {
                    int y = v - N;
                    for (int j = 0; j < d; j++) {
                        int u = invp[j][y];
                        if (vis[u] != stampv) { vis[u] = stampv; qbuf[qt++] = u; }
                    }
                }
            }
        }
        bad += 2L * N - qt;
    }
    return bad;
}

/* Anneal S until cost 0 (returns 1) or until the deadline (returns 0). Requires N > d. */
static int anneal(double until) {
    long cur = cost();
    double T = 1.0;
    for (long it = 1; cur > 0; it++) {
        if ((it & 31) == 0 && now() > until) return 0;
        int j = rndint(d), g;
        do { g = rndint(N); } while (in_S_n(g, d));
        int old = S[j];
        S[j] = g;
        update_row(j);
        long nc = cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            S[j] = old;
            update_row(j);
        }
        T *= 0.9995;
        if (T < 0.2) T = 1.0;
    }
    return 1;
}

static long moore_bound(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static void print_graph(void) {
    long m = (long)N * d;
    printf("%d %ld\n", 2 * N, m);
    for (int x = 0; x < N; x++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", x, N + perm[j][x]);
}

/* ---------------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 2 || D < 2 || d > MAXDEG) {
        printf("1 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    glist = malloc(sizeof(Grp) * MAXGROUPS);
    if (!glist) return 1;

    /* Start: K_{d,d} as the cyclic Haar graph over Z_d with S = all of Z_d. */
    Grp kdd = {1, d, 0};
    Grp bestG = kdd;
    int bestN = d;
    int bestS[MAXDEG];
    for (int j = 0; j < d; j++) bestS[j] = j;

    long moore = moore_bound();
    while (now() < t_end) {
        int Nt = bestN + 1;
        if (2L * Nt > moore || Nt > MAXG) break;
        enum_groups(Nt);
        if (gcount == 0) break;
        int found = 0;
        while (!found && now() < t_end) {
            Grp G = glist[rndint(gcount)];
            set_group(G);
            random_S();
            double until = now() + ATTEMPT;
            if (until > t_end) until = t_end;
            if (anneal(until)) {
                found = 1;
                bestG = G;
                bestN = N;
                memcpy(bestS, S, sizeof(int) * d);
            }
        }
        if (!found) break;
    }

    /* Rebuild the best state and verify it; fall back to K_{d,d} if anything is off. */
    set_group(bestG);
    memcpy(S, bestS, sizeof(int) * d);
    update_all();
    if (cost() != 0) {
        set_group(kdd);
        for (int j = 0; j < d; j++) S[j] = j;
        update_all();
    }
    print_graph();
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


def fallback(d, D):
    """Always-valid simple graph for (d, D)."""
    if D >= 2:
        return lib.haar_graph(d, range(d))   # K_{d,d}, diameter 2
    if D == 1:
        return (2, [(0, 1)])
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else fallback(d, D)
    if not lib.is_valid(*best, d, D):
        best = fallback(d, D)
    if d < 2 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 8)
        out = lib.parse_graph_text(text)
    except Exception:
        return best
    if out[0] > best[0] and lib.is_valid(*out, d, D):
        best = out
    return best
