"""Bi-Cayley / voltage-lift search for the weak targets, with a safe Python fallback.

Construction (new in this version): instead of growing a parent graph, the C engine
searches directly for a bipartite lift of a small base multigraph with p vertices per
side over a random semidirect group Z_m x| Z_k (order N, total 2pN vertices).
Each layer t is a permutation pi_t of the p base vertices plus one voltage g_{t,i} per
A-vertex, so every vertex has degree d and the lift is simple when no two darts clash.

Because left translation by the group is an automorphism, the diameter is <= D iff
BFS from the 2p base-identity vertices reaches everything within D steps. That makes
each cost evaluation cheap. Simulated annealing over voltages and permutations drives
the cost (unreached vertices plus duplicate-dart penalties) to zero. The group order N
ramps upward with exponential steps and halving on failure.

Python keeps the best known start (projective plane, Araujo-Pardo-Lopez, or K_{d,d}),
runs the C engine under a conservative budget, validates its output with lib.is_valid,
and returns whichever valid graph is larger. Any failure falls back to the start.
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
#define MAXP 2
#define MAXH 4096
#define MAXV 8192
#define PEN 20
#define STALL 3000

static int d, D;
static long moore;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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

/* ---------------------------------------------------------------- groups */

/* Z_m x|_r Z_k with m*k = N; element (a,b) is coded a*k+b; identity is 0. */
typedef struct {
    int N, m, k, r;
    int rp[MAXH]; /* rp[b] = r^b mod m */
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)(((long)a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int ginv(const Grp *G, int x) {
    int a = x / G->k, b = x % G->k;
    int nb = (G->k - b) % G->k;           /* r^k = 1, so r^{-b} = r^{k-b} */
    long t = (long)G->rp[nb] * a % G->m;
    int na = (int)((G->m - t) % G->m);
    return na * G->k + nb;
}

/* Uniformly random semidirect group of order N (cyclic/abelian cases included). */
static int random_group(int N, Grp *G) {
    long cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rlo = 0, rhi = 1;
        if (m > 1) { rlo = 1; rhi = m; }
        for (int r = rlo; r < rhi; r++) {
            if (m > 1) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
            }
            cnt++;
            long bound = cnt < 1000000000L ? cnt : 1000000000L;
            if (rndint((int)bound) == 0) { G->m = m; G->k = k; G->r = r; }
        }
    }
    if (!cnt) return 0;
    G->N = N;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ---------------------------------------------------------------- lifts */

/* Layer t joins A_i to B_{pi[t][i]} with voltage g[t][i]:
 * A_{i,x} ~ B_{pi[t][i], x*g[t][i]}. Each A and B vertex gets exactly d neighbours. */
typedef struct {
    int p;
    int pi[MAXD][MAXP];
    int g[MAXD][MAXP];
} Lift;

static int nb[MAXV][MAXD];
static int pinv[MAXD][MAXP];
static int distv[MAXV], queue_[MAXV];

/* Cost = (vertices not within D of a base identity, summed over the 2p base identities)
 * + PEN per duplicate dart. Zero iff the lift is simple, bipartite and has diameter <= D. */
static long lift_cost(const Lift *L, const Grp *G) {
    int p = L->p, N = G->N, V = 2 * p * N;
    long pen = 0;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < p; i++) pinv[t][L->pi[t][i]] = i;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < p; i++) {
            int j = L->pi[t][i];
            for (int t2 = 0; t2 < t; t2++)
                if (L->pi[t2][i] == j && L->g[t2][i] == L->g[t][i]) pen++;
            for (int x = 0; x < N; x++)
                nb[i * N + x][t] = (p + j) * N + gmul(G, x, L->g[t][i]);
        }
    for (int t = 0; t < d; t++)
        for (int j = 0; j < p; j++) {
            int i = pinv[t][j];
            int gi = ginv(G, L->g[t][i]);
            for (int y = 0; y < N; y++)
                nb[(p + j) * N + y][t] = i * N + gmul(G, y, gi);
        }
    long cost = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = s * N;
        for (int v = 0; v < V; v++) distv[v] = -1;
        int head = 0, tail = 0;
        queue_[tail++] = src;
        distv[src] = 0;
        while (head < tail) {
            int v = queue_[head++];
            if (distv[v] >= D) continue;
            for (int t = 0; t < d; t++) {
                int u = nb[v][t];
                if (distv[u] < 0) {
                    distv[u] = distv[v] + 1;
                    queue_[tail++] = u;
                }
            }
        }
        cost += V - tail;
    }
    return cost + pen * PEN;
}

static void random_lift(Lift *L, int p, int N) {
    L->p = p;
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            L->pi[t][i] = perm[i];
            L->g[t][i] = rndint(N);
        }
    }
}

static void mutate(Lift *L, int N) {
    int p = L->p;
    if (p == 1 || rnd01() < 0.6) {
        int t = rndint(d), i = rndint(p);
        L->g[t][i] = rndint(N);
    } else {
        int t = rndint(d), i1 = rndint(p), i2 = rndint(p);
        if (i1 == i2) i2 = (i1 + 1) % p;
        int s = L->pi[t][i1];
        L->pi[t][i1] = L->pi[t][i2];
        L->pi[t][i2] = s;
    }
}

static Lift solL;
static Grp solG;

/* Simulated annealing on one random group and lift shape. */
static int anneal(int N, int p, double until) {
    static Grp G;
    static Lift L, T2;
    if (!random_group(N, &G)) return 0;
    random_lift(&L, p, N);
    long cur = lift_cost(&L, &G);
    long bestc = cur;
    int stall = 0;
    for (long it = 0;; it++) {
        if (cur == 0) {
            solL = L;
            solG = G;
            return 1;
        }
        if ((it & 31) == 0 && now() > until) return 0;
        if (stall > STALL) return 0;
        T2 = L;
        mutate(&T2, N);
        long c = lift_cost(&T2, &G);
        double temp = 0.6;
        if (c <= cur || rnd01() < exp(-(double)(c - cur) / temp)) {
            L = T2;
            cur = c;
            if (cur < bestc) { bestc = cur; stall = 0; }
            else stall++;
        } else {
            stall++;
        }
    }
}

/* Keep trying (random group, random p in {1,2}) until success or the deadline. */
static int attempt(int N, double until) {
    while (now() < until) {
        if (2L * N > moore || 2L * N > MAXV || N > MAXH) return 0;
        int p = 1 + rndint(2);
        if (2L * p * N > moore || 2L * p * N > MAXV) p = 1;
        if (anneal(N, p, until)) return 1;
    }
    return 0;
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
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = moore_bound();

    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    static Grp bestG;
    static Lift bestL;
    int best_n = 0;
    long lo = d;
    long step = 1;

    if (attempt((int)lo, t_end)) {
        best_n = 2 * solL.p * (int)lo;
        bestL = solL;
        bestG = solG;
    }

    /* Ramp the group order N upward; double the step on success, halve on failure. */
    while (now() < t_end) {
        long target = lo + step;
        if (target > MAXH || 2 * target > moore) {
            if (step > 1) { step = 1; continue; }
            break;
        }
        double left = t_end - now();
        double slice = left * 0.3;
        if (slice < 0.3) slice = left;
        if (attempt((int)target, now() + slice)) {
            lo = target;
            step *= 2;
            int n = 2 * solL.p * (int)target;
            if (n > best_n) {
                best_n = n;
                bestL = solL;
                bestG = solG;
            }
        } else if (step > 1) {
            step /= 2;
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    int p = bestL.p, N = bestG.N, V = 2 * p * N;
    printf("%d %d\n", V, p * N * d);
    for (int t = 0; t < d; t++)
        for (int i = 0; i < p; i++) {
            int j = bestL.pi[t][i];
            for (int x = 0; x < N; x++)
                printf("%d %d\n", i * N + x, (p + j) * N + gmul(&bestG, x, bestL.g[t][i]));
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
    if start is None:
        start = lib.haar_graph(d, range(d))           # K_{d,d}, valid for D >= 2
    best = start
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)]) if lib.is_valid(2, [(0, 1)], d, D) else (1, [])

    # Leave margin for compilation and process overhead.
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the engine
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=None,
                             timeout=budget + 5)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass   # keep the valid fallback
    return best
