import math
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lifts over semidirect products Z_m x| Z_k.
#
# Vertices: A_x = x (0 <= x < G), B_y = G + y. Edge A_x ~ B_{x*s} for s in S,
# |S| = d, distinct. Left multiplication is an automorphism, so the graph is
# valid iff A_identity and B_identity reach every vertex within D steps.
# Search: simulated annealing over S, restarted over random groups of order G.
# G is increased while successes continue; the largest valid lift is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define GCAP 20000
#define DCAP 256

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

typedef struct { int m, k, G; long long r; int *rp; } Grp;

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long long gcdll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a < 0 ? -a : a;
}

static void build_group(int G, int m, int k, long long r, Grp *g) {
    g->m = m; g->k = k; g->G = G; g->r = r;
    g->rp = (int *)malloc(sizeof(int) * (size_t)k);
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        g->rp[b] = (int)p;
        p = p * r % m;
    }
}

/* Element a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(const Grp *g, int x, int y) {
    int k = g->k, m = g->m;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    long long A = ((long long)a + (long long)g->rp[b] * c) % m;
    int B = (b + e) % k;
    return (int)(A * k + B);
}

static int ginv(const Grp *g, int x) {
    int k = g->k, m = g->m;
    int a = x / k, b = x % k;
    int nb = (k - b) % k;
    long long A = ((long long)g->rp[nb] * a) % m;
    A = (m - A) % m;
    return (int)(A * k + nb);
}

static int pick_group(int G, Grp *g) {
    int divs[512];
    int nd = 0;
    for (int i = 1; (long long)i * i <= G; i++) {
        if (G % i == 0) {
            if (nd < 512) divs[nd++] = i;
            if (i != G / i && nd < 512) divs[nd++] = G / i;
        }
    }
    for (int tries = 0; tries < 200; tries++) {
        int k = divs[rndint(nd)];
        int m = G / k;
        long long r = 1;
        if (k == 1) {
            r = 1;
        } else if (m == 1) {
            r = 0;
        } else {
            int mode = rndint(10);
            if (mode < 2) {
                r = 1; /* abelian Z_m x Z_k */
            } else {
                int ok = 0;
                if (k == 2 && mode < 5) {
                    r = m - 1;
                    if (gcdll(r, m) == 1 && powmod(r, 2, m) == 1 % m) ok = 1;
                }
                for (int t = 0; !ok && t < 300; t++) {
                    r = 1 + rndint(m - 1);
                    if (gcdll(r, m) == 1 && powmod(r, k, m) == 1 % m) ok = 1;
                }
                if (!ok) continue;
            }
        }
        build_group(G, m, k, r, g);
        return 1;
    }
    return 0;
}

static int bufA[2 * GCAP], bufB[2 * GCAP];
static unsigned char vis[2 * GCAP];

static int bfs_reach(const Grp *g, const int *S, const int *Si, int d, int D, int src) {
    int G = g->G;
    memset(vis, 0, (size_t)(2 * G));
    int *cur = bufA, *nxt = bufB;
    int nc = 1, cnt = 1;
    cur[0] = src;
    vis[src] = 1;
    for (int step = 0; step < D && nc > 0; step++) {
        int nn = 0;
        for (int t = 0; t < nc; t++) {
            int v = cur[t];
            if (v < G) {
                for (int i = 0; i < d; i++) {
                    int w = G + gmul(g, v, S[i]);
                    if (!vis[w]) { vis[w] = 1; nxt[nn++] = w; }
                }
            } else {
                int y = v - G;
                for (int i = 0; i < d; i++) {
                    int w = gmul(g, y, Si[i]);
                    if (!vis[w]) { vis[w] = 1; nxt[nn++] = w; }
                }
            }
        }
        cnt += nn;
        int *tmp = cur; cur = nxt; nxt = tmp;
        nc = nn;
    }
    return cnt;
}

static int cost_of(const Grp *g, const int *S, const int *Si, int d, int D) {
    int G = g->G;
    int ca = bfs_reach(g, S, Si, d, D, 0);
    int cb = bfs_reach(g, S, Si, d, D, G);
    return (2 * G - ca) + (2 * G - cb);
}

static int attempt(const Grp *g, int d, int D, double dl, int iters, int *S, int *Si) {
    int G = g->G;
    if (G < d) return 0;
    for (int i = 0; i < d; i++) {
        int e;
        for (;;) {
            e = rndint(G);
            int dup = 0;
            for (int j = 0; j < i; j++) if (S[j] == e) { dup = 1; break; }
            if (!dup) break;
        }
        S[i] = e;
        Si[i] = ginv(g, e);
    }
    int cost = cost_of(g, S, Si, d, D);
    double T0 = 3.0 + (double)G / 200.0;
    for (int t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if ((t & 255) == 0 && now_s() > dl) break;
        double T = T0 * (1.0 - (double)t / (double)iters) + 0.05;
        int i = rndint(d);
        int e;
        for (;;) {
            e = rndint(G);
            int dup = 0;
            for (int j = 0; j < d; j++) if (S[j] == e) { dup = 1; break; }
            if (!dup) break;
        }
        int old = S[i], oldi = Si[i];
        S[i] = e;
        Si[i] = ginv(g, e);
        int c2 = cost_of(g, S, Si, d, D);
        int delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            S[i] = old;
            Si[i] = oldi;
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int G0 = atoi(argv[5]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    if (d < 2 || d > DCAP || D < 2 || G0 < 1) { printf("0 0\n"); return 0; }

    double deadline = now_s() + tl;
    int S[DCAP], Si[DCAP], bestS[DCAP];
    int bestG = 0, bm = 0, bk = 0;
    long long br = 0;
    int G = G0;
    const int ATT = 1500;

    while (G <= GCAP) {
        double t_now = now_s();
        if (t_now >= deadline) break;
        double remain = deadline - t_now;
        double slice_end = t_now + (bestG == 0 ? 0.6 * remain : 0.5 * remain);
        int found = 0;
        Grp g;
        while (now_s() < slice_end) {
            if (!pick_group(G, &g)) break;
            int ok = attempt(&g, d, D, slice_end, ATT, S, Si);
            if (ok) {
                found = 1;
                bm = g.m; bk = g.k; br = g.r;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
                free(g.rp);
                break;
            }
            free(g.rp);
        }
        if (!found) break;
        bestG = G;
        G++;
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    Grp g;
    build_group(bestG, bm, bk, br, &g);
    long long me = (long long)bestG * d;
    printf("%d %lld\n", 2 * bestG, me);
    for (int x = 0; x < bestG; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, bestG + gmul(&g, x, bestS[i]));
    free(g.rp);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: exact constructions, C search, and a valid fallback.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid whenever D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact projective-plane construction (diameter 3).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley lift search in C, starting from a size that is usually easy.
    if d >= 2 and D >= 2:
        G0 = max(best[0] // 2 + 1, lib.moore_bound(d, D) // 10)
        cbudget = max(1.0, budget - 1.5)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{cbudget:.3f}", G0],
                            timeout=max(2.0, time_limit - 3.0))
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
