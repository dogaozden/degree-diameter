"""Wide bi-Cayley lift search (C engine) with algebraic and K_{d,d} fallbacks.

Change from the parent: the C engine samples base graphs with up to 12 vertices per side
(the parent stopped at 8) and mixes direct products Z_m x Z_k with semidirect products
Z_m x| Z_k. It chooses base sizes with a bandit rule and uses a monotonic wall clock.
The Python annealing fallback and the generalized-quadrangle construction are removed.
Every candidate is checked with lib.is_valid before it is kept, and K_{d,d} is the
floor.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXK 12
#define PENALTY 1000
#define NK2 22

typedef uint64_t u64;

static u64 rs;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int n) { int v = (int)(rndu() * n); return v >= n ? n - 1 : v; }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long gcdll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group Z_m x|_r Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b + e). */
typedef struct { int m, k2, G; long long r; int pw[64]; } Group;
static Group grp;

static void set_group(int m, int k2, long long r) {
    grp.m = m; grp.k2 = k2; grp.G = m * k2; grp.r = r;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) { grp.pw[b] = (int)p; p = (p * r) % m; }
}

static int gmul(int x, int y) {
    int k2 = grp.k2, m = grp.m;
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = (a + (long long)grp.pw[b] * c) % m;
    return (int)(t * k2 + (b + e) % k2);
}

static int ginv(int x) {
    int k2 = grp.k2, m = grp.m;
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    long long t = ((long long)grp.pw[nb] * a) % m;
    long long na = (m - t) % m;
    return (int)(na * k2 + nb);
}

static int DEG, D_, K, G, N;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int *nbr = NULL;     /* nbr[l*N + v] */
static u64 *ra = NULL, *rb = NULL;
static u64 FULL;

static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static void set_dart(int l, int i) {
    int p = layers[l][i], s = S[l][i];
    int sinv = ginv(s);
    int *nl = nbr + (size_t)l * N;
    int q = K + p;
    for (int g = 0; g < G; g++) nl[i * G + g] = q * G + gmul(g, s);
    for (int h = 0; h < G; h++) nl[q * G + h] = i * G + gmul(h, sinv);
}

/* Returns the number of (vertex, representative) pairs farther than D apart. */
static int reach_eval(void) {
    for (int v = 0; v < N; v++) ra[v] = 0;
    for (int b = 0; b < 2 * K; b++) ra[b * G] |= (u64)1 << b;
    for (int round = 0; round < D_; round++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 u = ra[v];
            for (int l = 0; l < DEG; l++) u |= ra[nbr[(size_t)l * N + v]];
            rb[v] = u;
            if (u != ra[v]) changed = 1;
        }
        u64 *t = ra; ra = rb; rb = t;
        if (!changed) break;
    }
    int unr = 0;
    for (int v = 0; v < N; v++) unr += pc64(FULL & ~ra[v]);
    return unr;
}

static long long eval_cost(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < DEG; l++)
            for (int l2 = l + 1; l2 < DEG; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) dup++;
    int unr = reach_eval();
    return (long long)unr + (long long)PENALTY * dup;
}

static void record_solution(void) {
    int m = K * G * DEG;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    if (!e) return;
    int idx = 0;
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < DEG; l++) {
            e[2 * idx] = u;
            e[2 * idx + 1] = nbr[(size_t)l * N + u];
            idx++;
        }
    free(best_e);
    best_e = e;
    best_m = m;
    best_n = N;
}

static int anneal(long iters, long patience, double deadline) {
    long long cost = eval_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long long bestc = cost;
    long last = 0;
    for (long t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if ((t & 31) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rndu() < 0.25) {
            int l = rndint(DEG);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
            set_dart(l, i1); set_dart(l, i2);
            long long c2 = eval_cost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
                set_dart(l, i1); set_dart(l, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rndu() < 0.4) {
            for (int tries = 0; tries < 30 && l < 0; tries++) {
                int v = rndint(N);
                if ((ra[v] & FULL) != FULL) {
                    int block = v / G;
                    if (block < K) {
                        i = block;
                        l = rndint(DEG);
                    } else {
                        l = rndint(DEG);
                        for (int j = 0; j < K; j++)
                            if (layers[l][j] == block - K) { i = j; break; }
                    }
                }
            }
        }
        if (l < 0) { l = rndint(DEG); i = rndint(K); }

        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i);
        long long c2 = eval_cost();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) { bestc = cost; last = t; }
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static const int K2LIST[NK2] = {1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 24, 30, 36};

static int sample_group(int target, int *pm, int *pk2, long long *pr) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2LIST[rndint(NK2)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long long r = -1;
        if (k2 == 1 || m <= 2 || rndu() < 0.3) {
            r = 1;  /* direct product Z_m x Z_k2 (abelian) */
        } else {
            for (int t = 0; t < 60; t++) {
                long long c = 2 + rndint(m - 2);
                if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
            if (r < 0) continue;
        }
        *pm = m; *pk2 = k2; *pr = r;
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int n0 = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    DEG = d;
    D_ = D;
    rs = 0x9E3779B97F4A7C15ULL ^ (u64)(seed * 2654435761UL + 12345UL);
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd64();

    double deadline = now() + tl;
    best_n = n0;
    best_m = 0;
    best_e = NULL;
    static int trials[MAXK + 1], wins[MAXK + 1];

    while (now() < deadline) {
        int k;
        if (rndu() < 0.25) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double s = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.05 * rndu();
                if (s > bs) { bs = s; k = kk; }
            }
        }
        int base = best_n / (2 * k);
        int spread = base / 6 + 2;
        int target = base + 1 + rndint(spread);
        if (target < 2) target = 2;

        int m, k2;
        long long r;
        if (!sample_group(target, &m, &k2, &r)) continue;
        set_group(m, k2, r);
        G = grp.G;
        K = k;
        N = 2 * K * G;
        if (N <= best_n) continue;

        FULL = (((u64)1) << (2 * K)) - 1;
        nbr = malloc(sizeof(int) * (size_t)DEG * N);
        ra = malloc(sizeof(u64) * (size_t)N);
        rb = malloc(sizeof(u64) * (size_t)N);
        if (!nbr || !ra || !rb) {
            free(nbr); free(ra); free(rb);
            nbr = NULL; ra = NULL; rb = NULL;
            break;
        }

        for (int l = 0; l < DEG; l++) {
            for (int i = 0; i < K; i++) layers[l][i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = layers[l][i]; layers[l][i] = layers[l][j]; layers[l][j] = tmp;
            }
        }
        for (int l = 0; l < DEG; l++)
            for (int i = 0; i < K; i++) S[l][i] = rndint(G);
        for (int l = 0; l < DEG; l++)
            for (int i = 0; i < K; i++) set_dart(l, i);

        trials[K]++;
        int ok = anneal(10000, 2000, deadline);
        if (ok) {
            wins[K]++;
            record_solution();
        }
        free(nbr); free(ra); free(rb);
        nbr = NULL; ra = NULL; rb = NULL;
    }

    if (best_m == 0) {
        printf("0 0\n");
    } else {
        printf("%d %d\n", best_n, best_m);
        for (int j = 0; j < best_m; j++)
            printf("%d %d\n", best_e[2 * j], best_e[2 * j + 1]);
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Algebraic baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension: add vertices using spare degree; every kept graph is valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return a 2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    final_deadline = start + max(1.0, time_limit - 5.0)

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

    # Exact constructions for D = 3.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass
        if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
            try:
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)
            except Exception:
                pass
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    # Main engine: wide bi-Cayley lifts searched in C.
    c_budget = min(0.75 * time_limit, time_limit - 12.0) - (time.monotonic() - start)
    if c_budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), best_n],
                            stdin_graph=None, timeout=c_budget + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Use spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline - 1.0:
        rng = random.Random(seed)
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
