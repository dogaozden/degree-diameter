"""Cayley-lift search for bipartite degree-diameter graphs.

Main idea (new in this version): a bipartite Cayley graph over a metacyclic group G = Z_m x| Z_k
with parts A = G and B = G, and edges a_x -- b_{x s} for s in a set S of d distinct group elements.
Left translations are automorphisms, so the diameter condition reduces to two BFS runs (from a_e and
from b_e), not an all-pairs check. Simulated annealing then searches over S for each target order N,
growing N one step at a time from the best order found so far.

Safety: Python validates the start graph and the C output with lib.is_valid, and keeps the
best valid graph it has. Any C failure or timeout falls back to that graph.
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

#define MAXG 1200
#define MAXV (2 * MAXG)
#define MAXDEG 16
#define MAXE (MAXV * MAXDEG)

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

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

/* ------------------------------------------------------------ best graph store */

static int bestEu[MAXE], bestEv[MAXE];
static int best_m = 0, best_n = 0;

/* ------------------------------------------------------------ full validity check */

static int sadj[MAXV][MAXDEG];
static int sdeg[MAXV];
static int sdist[MAXV], sq[MAXV], sside[MAXV];

static int check_graph(int n, int m, const int *eu, const int *ev) {
    if (n <= 0 || n > MAXV || m < 0 || m > MAXE) return 0;
    for (int v = 0; v < n; v++) sdeg[v] = 0;
    for (int e = 0; e < m; e++) {
        int u = eu[e], v = ev[e];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (sdeg[u] >= MAXDEG || sdeg[v] >= MAXDEG) return 0;
        sadj[u][sdeg[u]++] = v;
        sadj[v][sdeg[v]++] = u;
    }
    for (int v = 0; v < n; v++) {
        if (sdeg[v] > d) return 0;
        for (int i = 0; i < sdeg[v]; i++)
            for (int j = 0; j < i; j++)
                if (sadj[v][i] == sadj[v][j]) return 0;
    }
    /* bipartite */
    for (int v = 0; v < n; v++) sside[v] = -1;
    for (int s = 0; s < n; s++) {
        if (sside[s] >= 0) continue;
        int head = 0, tail = 0;
        sside[s] = 0;
        sq[tail++] = s;
        while (head < tail) {
            int v = sq[head++];
            for (int i = 0; i < sdeg[v]; i++) {
                int u = sadj[v][i];
                if (sside[u] < 0) { sside[u] = 1 - sside[v]; sq[tail++] = u; }
                else if (sside[u] == sside[v]) return 0;
            }
        }
    }
    /* diameter <= D */
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) sdist[v] = -1;
        int head = 0, tail = 0;
        sdist[s] = 0;
        sq[tail++] = s;
        while (head < tail) {
            int v = sq[head++];
            if (sdist[v] >= D) continue;
            for (int i = 0; i < sdeg[v]; i++) {
                int u = sadj[v][i];
                if (sdist[u] < 0) { sdist[u] = sdist[v] + 1; sq[tail++] = u; }
            }
        }
        if (tail != n) return 0;
    }
    return 1;
}

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int N;                  /* group order = number of elements of G */
static int MT[MAXG * MAXG];    /* MT[x*N + y] = x*y */
static int INV[MAXG];
static int rp[MAXG];
static int gm, gk, gr;

/* Uniformly random metacyclic group of order `order`, among all (m, k, r) with
 * m*k = order, gcd(r, m) = 1, r^k = 1 mod m. Always succeeds (cyclic group exists). */
static void random_group(int order) {
    long count = 0;
    int bm = 1, bk = order, br = 1;
    for (int m = 1; m <= order; m++) {
        if (order % m) continue;
        int k = order / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    gm = bm; gk = bk; gr = br;
    rp[0] = 1 % gm;
    for (int b = 1; b < gk; b++) rp[b] = (int)((long)rp[b - 1] * gr % gm);
}

/* Element code x = a*k + b represents (a, b); (a,b)(c,e) = (a + r^b c, b + e). */
static void build_group(void) {
    for (int x = 0; x < N; x++) {
        int a = x / gk, b = x % gk;
        for (int y = 0; y < N; y++) {
            int c = y / gk, e = y % gk;
            MT[x * N + y] = (int)((a + (long)rp[b] * c) % gm) * gk + (b + e) % gk;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
}

/* ------------------------------------------------------------ Cayley bipartite graph */

/* Vertices: A-vertex x is index x, B-vertex y is index N + y.
 * A-vertex x ~ B-vertex x*s for s in S. B-vertex y ~ A-vertex y*s^{-1}. */
static int S[MAXDEG], SI[MAXDEG];
static int vis[MAXV], Q[MAXV];
static int vstamp = 0;

static void bfs(int src, int *cntA, int *cntB) {
    vstamp++;
    int head = 0, tail = 0;
    vis[src] = vstamp;
    Q[tail++] = src;
    for (int lev = 0; lev < D && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int v = Q[head++];
            if (v < N) {
                const int *row = MT + (size_t)v * N;
                for (int i = 0; i < d; i++) {
                    int u = N + row[S[i]];
                    if (vis[u] != vstamp) { vis[u] = vstamp; Q[tail++] = u; }
                }
            } else {
                const int *row = MT + (size_t)(v - N) * N;
                for (int i = 0; i < d; i++) {
                    int u = row[SI[i]];
                    if (vis[u] != vstamp) { vis[u] = vstamp; Q[tail++] = u; }
                }
            }
        }
    }
    int a = 0, b = 0;
    for (int i = 0; i < tail; i++) {
        if (Q[i] < N) a++;
        else b++;
    }
    *cntA = a;
    *cntB = b;
}

/* Number of violations. Zero iff the Cayley graph has diameter <= D.
 * By left translation: A-A and A-B pairs are covered by the ball of a_e,
 * B-B pairs by the ball of b_e. */
static int cost_now(void) {
    int a1, b1, a2, b2;
    bfs(0, &a1, &b1);
    bfs(N, &a2, &b2);
    return (N - a1) + (N - b1) + (N - b2);
}

static int in_set(int g, int upto) {
    for (int j = 0; j < upto; j++)
        if (S[j] == g) return 1;
    return 0;
}

/* Simulated annealing over S (d distinct elements). Returns 1 if cost reaches 0. */
static int sa_run(long iters, double T0, double T1) {
    for (int i = 0; i < d; i++) {
        int g;
        do { g = rndint(N); } while (in_set(g, i));
        S[i] = g;
        SI[i] = INV[g];
    }
    int cur = cost_now();
    if (cur == 0) return 1;
    double lr = log(T1 / T0);
    for (long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && now() > t_end) return 0;
        double T = T0 * exp(lr * (double)it / (double)iters);
        int i = rndint(d);
        int g;
        do { g = rndint(N); } while (in_set(g, d));
        int old = S[i], oldi = SI[i];
        S[i] = g;
        SI[i] = INV[g];
        int nc = cost_now();
        if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            S[i] = old;
            SI[i] = oldi;
        }
    }
    return 0;
}

static void store_cayley(void) {
    int m = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) {
            bestEu[m] = x;
            bestEv[m] = N + MT[x * N + S[i]];
            m++;
        }
    best_m = m;
    best_n = 2 * N;
}

/* ------------------------------------------------------------ output */

static void print_best(void) {
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", bestEu[e], bestEv[e]);
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    /* Optional valid start graph. */
    static int seu[MAXE], sev[MAXE];
    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) == 2 && sn > 0 && sm >= 0 && sm <= MAXE) {
        int ok = 1;
        for (int e = 0; e < sm && ok; e++)
            if (scanf("%d %d", &seu[e], &sev[e]) != 2) ok = 0;
        if (ok && check_graph(sn, sm, seu, sev)) {
            best_n = sn;
            best_m = sm;
            memcpy(bestEu, seu, sizeof(int) * (size_t)sm);
            memcpy(bestEv, sev, sizeof(int) * (size_t)sm);
        }
    }

    if (d >= 2 && d <= MAXDEG && D >= 2) {
        long moore = moore_bound();
        int bestN = best_n / 2;
        while (now() < t_end) {
            int target = bestN + 1;
            if (rndint(4) == 0) target += rndint(1 + bestN / 40);
            if (target <= d) target = d + 1;
            if (target > MAXG || 2L * target > moore) target = bestN + 1;
            if (target <= d) target = d + 1;
            if (target > MAXG || 2L * target > moore) break;
            N = target;
            random_group(N);
            build_group();
            if (sa_run(40000, 2.0, 0.2)) {
                store_cayley();
                bestN = N;
            }
        }
    }

    /* Final safety check; fall back to K_{d,d} if anything is off. */
    if (best_m == 0 || !check_graph(best_n, best_m, bestEu, bestEv)) {
        best_m = 0;
        best_n = 2 * d;
        if (d >= 1 && d * d <= MAXE) {
            for (int a = 0; a < d; a++)
                for (int b = 0; b < d; b++) {
                    bestEu[best_m] = a;
                    bestEv[best_m] = d + b;
                    best_m++;
                }
        } else {
            best_n = 0;
        }
    }
    print_best();
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
    if D <= 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)]) if d >= 1 else (1, [])

    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing to gain

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0 or d < 2 or d > 16:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the safe fallback
    return best
