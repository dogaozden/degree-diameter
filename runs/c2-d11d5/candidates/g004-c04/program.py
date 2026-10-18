"""Single-orbit bi-Cayley search over Z_m x| Z_k2 with a reachability-only objective.

Construction: for k = 1 the bipartite graph has parts A_g and B_h (g, h in G), with
A_g adjacent to B_{g*s} for each of d distinct connection elements s. Left multiplication
is an automorphism that fixes each part, so the graph has diameter <= D iff the balls of
radius D around A_1 and B_1 cover the whole graph. The C engine anneals over the d
connection elements only, with a cost equal to the number of uncovered vertices from those
two sources. Group orders are pushed just above the current best, and sizes are sampled
from several group families. Multiplication tables are precomputed per element, so each
evaluation is a pure table-lookup BFS.

Fallbacks: K_{d,d} (diameter 2) and the projective-plane incidence graph (diameter 3) are
built first. Every candidate is checked with lib.is_valid before it is kept.
"""
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK2 64

typedef uint64_t u64;

static u64 rs;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int n) { int v = (int)(rndu() * n); return v >= n ? n - 1 : v; }

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long long gcdll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

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

static int DEG, DD;
static int M, K2, G;
static long long RR;
static int pw[MAXK2];
static int *ga = NULL, *gb = NULL, *ginv_t = NULL;
static int *PL = NULL, *PR = NULL;   /* PL[l*G+x] = x*S[l]; PR[l*G+h] = h*S[l]^{-1} */
static int *stamp = NULL, *qa = NULL, *qb = NULL;
static int stampc = 0;
static int S[MAXD], Si[MAXD];

static void free_group(void) {
    free(ga); free(gb); free(ginv_t); free(PL); free(PR);
    free(stamp); free(qa); free(qb);
    ga = gb = ginv_t = PL = PR = stamp = qa = qb = NULL;
}

/* Group Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b + e). */
static void set_group(int m, int k2, long long r) {
    free_group();
    M = m; K2 = k2; G = m * k2; RR = r;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) { pw[b] = (int)p; p = (p * r) % m; }
    ga = malloc(sizeof(int) * (size_t)G);
    gb = malloc(sizeof(int) * (size_t)G);
    ginv_t = malloc(sizeof(int) * (size_t)G);
    PL = malloc(sizeof(int) * (size_t)DEG * G);
    PR = malloc(sizeof(int) * (size_t)DEG * G);
    stamp = calloc((size_t)2 * G, sizeof(int));
    qa = malloc(sizeof(int) * (size_t)2 * G);
    qb = malloc(sizeof(int) * (size_t)2 * G);
    stampc = 0;
    for (int x = 0; x < G; x++) { ga[x] = x / k2; gb[x] = x % k2; }
    for (int x = 0; x < G; x++) {
        int a = ga[x], b = gb[x];
        int nb = (K2 - b) % K2;
        long long t = ((long long)pw[nb] * a) % M;
        long long na = (M - t) % M;
        ginv_t[x] = (int)(na * K2 + nb);
    }
}

static inline int gmul(int x, int y) {
    int a = ga[x], b = gb[x], c = ga[y], e = gb[y];
    long long t = ((long long)a + (long long)pw[b] * c) % M;
    int s = b + e;
    if (s >= K2) s -= K2;
    return (int)(t * K2 + s);
}

static void set_elem(int l, int x) {
    S[l] = x;
    Si[l] = ginv_t[x];
    int *pl = PL + (size_t)l * G;
    int *pr = PR + (size_t)l * G;
    for (int g = 0; g < G; g++) {
        pl[g] = gmul(g, x);
        pr[g] = gmul(g, Si[l]);
    }
}

/* Number of vertices within distance DD of src. Vertex g < G is A_g; G + h is B_h. */
static int ball_size(int src) {
    stampc++;
    int *cur = qa, *nxt = qb;
    int nc = 1, cnt = 1;
    cur[0] = src;
    stamp[src] = stampc;
    for (int lev = 0; lev < DD && nc > 0; lev++) {
        int nn = 0;
        for (int i = 0; i < nc; i++) {
            int v = cur[i];
            if (v < G) {
                for (int l = 0; l < DEG; l++) {
                    int w = G + PL[(size_t)l * G + v];
                    if (stamp[w] != stampc) { stamp[w] = stampc; nxt[nn++] = w; }
                }
            } else {
                int h = v - G;
                for (int l = 0; l < DEG; l++) {
                    int w = PR[(size_t)l * G + h];
                    if (stamp[w] != stampc) { stamp[w] = stampc; nxt[nn++] = w; }
                }
            }
        }
        cnt += nn;
        int *t = cur; cur = nxt; nxt = t;
        nc = nn;
    }
    return cnt;
}

static long long eval_cost(void) {
    long long a = 2LL * G - ball_size(0);
    long long b = 2LL * G - ball_size(G);
    return a + b;
}

static int anneal(long iters, long patience, double deadline) {
    long long cost = eval_cost();
    if (cost == 0) return 1;
    double c0 = (double)cost;
    long long bestc = cost;
    long last = 0;
    for (long t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if ((t & 31) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.03 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.3) temp = 0.3;
        int l = rndint(DEG);
        int nw = rndint(G);
        int dup = 0;
        for (int i = 0; i < DEG; i++) if (S[i] == nw) { dup = 1; break; }
        if (dup) continue;
        int old = S[l];
        set_elem(l, nw);
        long long c2 = eval_cost();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) { bestc = cost; last = t; }
        } else {
            set_elem(l, old);
        }
    }
    return cost == 0;
}

static const int K2LIST[16] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 30, 36};

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int n0 = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    DEG = d;
    DD = D;
    rs = 0x9E3779B97F4A7C15ULL ^ (u64)(seed * 2654435761UL + 12345UL);
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd64();

    double deadline = now() + tl;
    int best_G = n0 / 2;
    if (best_G < DEG) best_G = DEG;
    int have = 0;
    int bestS[MAXD];
    int bM = 0, bK2 = 0;
    long long bR = 1;

    while (now() < deadline) {
        int spread = best_G / 40 + 2;
        int target = best_G + 1 + rndint(spread);
        int k2 = K2LIST[rndint(16)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long long r = 1;
        if (k2 == 2 && m > 2 && rndu() < 0.3) {
            r = m - 1;
        } else if (k2 > 1 && m > 2 && rndu() < 0.75) {
            for (int t = 0; t < 80; t++) {
                long long c = 2 + rndint(m - 2);
                if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
        }
        int Gn = m * k2;
        if (Gn <= best_G || Gn < DEG + 1) continue;

        set_group(m, k2, r);

        for (int l = 0; l < DEG; l++) {
            int x, ok;
            do {
                x = rndint(G);
                ok = 1;
                for (int i = 0; i < l; i++) if (S[i] == x) { ok = 0; break; }
            } while (!ok);
            set_elem(l, x);
        }

        long iters = 2000L + 4L * (long)G;
        long patience = iters / 2;
        if (anneal(iters, patience, deadline)) {
            best_G = G;
            have = 1;
            memcpy(bestS, S, sizeof(int) * (size_t)DEG);
            bM = M;
            bK2 = K2;
            bR = RR;
        }
    }

    if (!have) { printf("0 0\n"); return 0; }

    set_group(bM, bK2, bR);
    for (int l = 0; l < DEG; l++) set_elem(l, bestS[l]);
    printf("%d %d\n", 2 * G, G * DEG);
    for (int g = 0; g < G; g++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", g, G + PL[(size_t)l * G + g]);
    free_group();
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact construction: PG(2, q) has diameter 3.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main engine: C search over single-orbit bi-Cayley graphs.
    budget = max(1.0, 0.80 * time_limit - (time.monotonic() - t0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n],
                        stdin_graph=None, timeout=budget + 8.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
