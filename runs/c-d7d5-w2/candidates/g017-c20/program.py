import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine H (new, bold): simulated annealing over the connection set S of a
# Haar graph H(G, S) of a finite group G = Z_m x|_r Z_k2 (element (a, b) coded
# as a*k2 + b). Vertices a_x (0..N-1) and b_y (N..2N-1); a_x ~ b_{x*s} for s in S.
#
# The group acts by left translation, so the graph is vertex-transitive on each
# side. Hence the graph is valid iff every vertex is within D of a_0 and of b_0.
# Cost = (# vertices not within D of a_0) + (# vertices not within D of b_0).
# Each evaluation costs two BFS passes over 2N vertices.
#
# Usage: prog d D m k2 r seed slice_seconds
# Prints a valid graph ("2N  N*d" + edges) or "0 0".
# ----------------------------------------------------------------------------

HAAR_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64

static int d, D, m, k2, r, N;
static int S[MAXD];
static int *gm, *ginv, *powr, *dist, *queue;
static uint64_t rs = 1;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(clock_t t0) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int mulf(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = (a + (long long)powr[b] * c) % m;
    return (int)(t * k2 + (b + e) % k2);
}

static int in_set(int g) {
    for (int i = 0; i < d; i++) if (S[i] == g) return 1;
    return 0;
}

/* Number of vertices of the 2N-vertex graph NOT within distance D of src. */
static int bfs_bad(int src) {
    int V = 2 * N;
    for (int i = 0; i < V; i++) dist[i] = -1;
    int head = 0, tail = 0;
    dist[src] = 0;
    queue[tail++] = src;
    while (head < tail) {
        int u = queue[head++];
        int du = dist[u];
        if (du >= D) continue;
        if (u < N) {
            const int *row = gm + (size_t)u * N;
            for (int i = 0; i < d; i++) {
                int v = N + row[S[i]];
                if (dist[v] < 0) { dist[v] = du + 1; queue[tail++] = v; }
            }
        } else {
            int y = u - N;
            const int *row = gm + (size_t)y * N;
            for (int i = 0; i < d; i++) {
                int v = row[ginv[S[i]]];
                if (dist[v] < 0) { dist[v] = du + 1; queue[tail++] = v; }
            }
        }
    }
    return V - tail;
}

static int cost(void) {
    return bfs_bad(0) + bfs_bad(N);
}

int main(int argc, char **argv) {
    if (argc < 8) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    m = atoi(argv[3]);
    k2 = atoi(argv[4]);
    r = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (d < 1 || d > MAXD || D < 1 || m < 1 || k2 < 1) { printf("0 0\n"); return 0; }
    N = m * k2;
    if (N < 2 * d || N > 1500) { printf("0 0\n"); return 0; }
    if (gcd_int(r, m) != 1) { printf("0 0\n"); return 0; }

    powr = malloc(sizeof(int) * (size_t)k2);
    if (!powr) { printf("0 0\n"); return 0; }
    powr[0] = 1 % m;
    for (int b = 1; b < k2; b++) powr[b] = (int)((long long)powr[b - 1] * r % m);
    if (((long long)powr[k2 - 1] * r) % m != 1 % m) { printf("0 0\n"); return 0; }

    gm = malloc(sizeof(int) * (size_t)N * (size_t)N);
    ginv = malloc(sizeof(int) * (size_t)N);
    dist = malloc(sizeof(int) * (size_t)2 * N);
    queue = malloc(sizeof(int) * (size_t)2 * N);
    if (!gm || !ginv || !dist || !queue) { printf("0 0\n"); return 0; }

    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            gm[(size_t)x * N + y] = mulf(x, y);
    for (int x = 0; x < N; x++) {
        ginv[x] = -1;
        for (int y = 0; y < N; y++) {
            if (gm[(size_t)x * N + y] == 0) { ginv[x] = y; break; }
        }
        if (ginv[x] < 0) { printf("0 0\n"); return 0; }
    }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x51ED27ULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    int found = 0;
    while (!found && elapsed(t0) < slice) {
        for (int i = 0; i < d; i++) S[i] = -1;
        for (int i = 0; i < d; i++) {
            int g;
            do { g = rndint(N); } while (in_set(g));
            S[i] = g;
        }
        int cur = cost();
        if (cur == 0) { found = 1; break; }

        const int RL = 40000;
        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = 2.0 * (1.0 - (double)it / RL) + 0.05;
            int i = rndint(d);
            int g;
            do { g = rndint(N); } while (in_set(g));
            int old = S[i];
            S[i] = g;
            int nc = cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                S[i] = old;
            }
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", 2 * N, N * d);
        for (int x = 0; x < N; x++) {
            const int *row = gm + (size_t)x * N;
            for (int i = 0; i < d; i++) {
                printf("%d %d\n", x, N + row[S[i]]);
            }
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Engine A (from the parent): simulated annealing over the voltages of a
# bi-Cayley lift over Z_m x|_r Z_k2.
# ----------------------------------------------------------------------------

LIFT_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define STAG 8000

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int *POWR;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dI[e1] == dI[e2] && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = dI[e] * G, bb = (K + dJ[e]) * G;
        const int *pm = perm + (size_t)e * G;
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    const int LMAX = DIAM + 3;
    const int UNREACH_W = LMAX - DIAM + 2;
    int total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        for (int lv = 0; lv < LMAX && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                const int *au = adj + (size_t)u * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nxt[nn++] = v;
                    }
                }
            }
            reached += nn;
            if (lv + 1 > DIAM) total += (lv + 1 - DIAM) * nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += (N - reached) * UNREACH_W;
    }
    return total + PEN * dup;
}

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D K m k2 r seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    MM = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    uint64_t seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);

    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 4096) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    G = MM * K2;
    N = 2 * K * G;
    NE = DEG * K;

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dI = malloc(sizeof(int) * NE);
    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    bestJ = malloc(sizeof(int) * NE);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    int *p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt || !fr || !nx || !vis || !p) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 60000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.25) {
            for (int l = 0; l < DEG; l++) {
                for (int i = 0; i < K; i++) p[i] = i;
                for (int i = K - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = p[i]; p[i] = p[j]; p[j] = t;
                }
                for (int i = 0; i < K; i++) {
                    dI[l * K + i] = i;
                    dJ[l * K + i] = p[i];
                }
            }
            for (int e = 0; e < NE; e++) {
                dS[e] = rndint(G);
                set_perm(e);
            }
            T0 = 2.0;
        } else {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            for (int e = 0; e < NE; e++) set_perm(e);
            T0 = 0.8;
        }
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        int runBest = cur;
        int since = 0;
        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                }
            } else {
                int e = rndint(NE);
                int old = dS[e];
                int ns = rndint(G);
                if (ns == old) continue;
                dS[e] = ns;
                set_perm(e);
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    dS[e] = old;
                    set_perm(e);
                }
            }
            if (cur < bestCost) { bestCost = cur; save_best(); }
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + perm[(size_t)e * G + g]);
            }
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Engine B (from the parent): annealing repair on a general bipartite graph.
# ----------------------------------------------------------------------------

REPAIR_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define HM 700
#define NV (2 * HM)
#define WD ((NV + 63) / 64)
#define MAXDEG 16
#define MAXE (HM * MAXDEG)

static int d, D, hc, E;
static int deg[NV];
static int nb[NV][MAXDEG];
static int ea[MAXE], eb[MAXE];
static int eidx[HM * HM];
static uint64_t RA[NV][WD], RB[NV][WD];
static int sa[MAXE], sb[MAXE], sE;
static int ga[MAXE], gb[MAXE], gE;
static int cur_cost;
static uint64_t rs = 1;
static clock_t t0;
static double budget;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int adjq(int a, int b) { return eidx[a * HM + b] != 0; }

static void add_edge(int a, int b) {
    int va = a, vb = HM + b;
    eidx[a * HM + b] = E + 1;
    ea[E] = a; eb[E] = b; E++;
    nb[va][deg[va]++] = vb;
    nb[vb][deg[vb]++] = va;
}

static void del_nb(int v, int u) {
    for (int k = 0; k < deg[v]; k++) {
        if (nb[v][k] == u) {
            nb[v][k] = nb[v][deg[v] - 1];
            deg[v]--;
            return;
        }
    }
}

static void remove_pair(int a, int b) {
    int i = eidx[a * HM + b] - 1;
    eidx[a * HM + b] = 0;
    del_nb(a, HM + b);
    del_nb(HM + b, a);
    int last = E - 1;
    if (i != last) {
        ea[i] = ea[last];
        eb[i] = eb[last];
        eidx[ea[i] * HM + eb[i]] = i + 1;
    }
    E--;
}

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

/* Number of unordered active pairs at distance > D. */
static int cost(void) {
    int NA = 2 * hc;
    uint64_t (*cur)[WD] = RA, (*nxt)[WD] = RB;
    memset(RA, 0, sizeof(RA));
    for (int a = 0; a < hc; a++) {
        cur[a][a >> 6] |= 1ULL << (a & 63);
        int v = HM + a;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < D; step++) {
        for (int a = 0; a < hc; a++) {
            for (int s = 0; s < 2; s++) {
                int v = s ? HM + a : a;
                uint64_t *dst = nxt[v];
                memcpy(dst, cur[v], sizeof(uint64_t) * WD);
                for (int k = 0; k < deg[v]; k++) {
                    const uint64_t *src = cur[nb[v][k]];
                    for (int w = 0; w < WD; w++) dst[w] |= src[w];
                }
            }
        }
        uint64_t (*t)[WD] = cur;
        cur = nxt;
        nxt = t;
    }
    int bad = 0;
    for (int a = 0; a < hc; a++) {
        for (int s = 0; s < 2; s++) {
            int v = s ? HM + a : a;
            int pc = 0;
            for (int w = 0; w < WD; w++) pc += popc(cur[v][w]);
            bad += NA - pc;
        }
    }
    return bad / 2;
}

/* Random active vertex index on a side (0 = A, 1 = B) with deg < d, or -1. */
static int pick_spare(int side) {
    int cnt = 0, pick = -1;
    for (int a = 0; a < hc; a++) {
        int v = side ? HM + a : a;
        if (deg[v] < d) {
            cnt++;
            if (rndint(cnt) == 0) pick = a;
        }
    }
    return pick;
}

static void save_state(int *xa, int *xb, int *xE) {
    for (int i = 0; i < E; i++) { xa[i] = ea[i]; xb[i] = eb[i]; }
    *xE = E;
}

static void load_state(const int *xa, const int *xb, int xE) {
    for (int i = 0; i < E; i++) eidx[ea[i] * HM + eb[i]] = 0;
    memset(deg, 0, sizeof(deg));
    E = 0;
    for (int i = 0; i < xE; i++) add_edge(xa[i], xb[i]);
}

static void anneal_step(double T) {
    int old = cur_cost;
    int kind = rndint(10);

    if (kind < 3) {
        int a = pick_spare(0), b = pick_spare(1);
        if (a < 0 || b < 0 || adjq(a, b)) return;
        add_edge(a, b);
        cur_cost = cost();
        return;
    }

    if (kind < 7) {
        if (E < 2) return;
        int i = rndint(E), j = rndint(E);
        if (i == j) return;
        int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
        if (a1 == a2 || b1 == b2 || adjq(a1, b2) || adjq(a2, b1)) return;
        remove_pair(a1, b1);
        remove_pair(a2, b2);
        add_edge(a1, b2);
        add_edge(a2, b1);
        int nc = cost();
        if (nc <= old || rnd01() < exp(-(double)(nc - old) / T)) {
            cur_cost = nc;
            return;
        }
        remove_pair(a1, b2);
        remove_pair(a2, b1);
        add_edge(a1, b1);
        add_edge(a2, b2);
        return;
    }

    if (E < 1) return;
    int i = rndint(E);
    int a1 = ea[i], b1 = eb[i];
    int a, b;
    if (rndint(2)) {
        b = pick_spare(1);
        if (b < 0 || b == b1 || adjq(a1, b)) return;
        a = a1;
    } else {
        a = pick_spare(0);
        if (a < 0 || a == a1 || adjq(a, b1)) return;
        b = b1;
    }
    remove_pair(a1, b1);
    add_edge(a, b);
    int nc = cost();
    if (nc <= old || rnd01() < exp(-(double)(nc - old) / T)) {
        cur_cost = nc;
        return;
    }
    remove_pair(a, b);
    add_edge(a1, b1);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEFULL;
    if (rs == 0) rs = 1;
    t0 = clock();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (d < 1 || d > MAXDEG || D < 1 || n < 2 || (n & 1) || n / 2 > HM - 1) {
        printf("0 0\n");
        return 0;
    }
    int h0 = n / 2;
    hc = h0;
    E = 0;
    memset(deg, 0, sizeof(deg));
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u > v) { int t = u; u = v; v = t; }
        if (u < 0 || v >= n || u >= h0 || v < h0) continue;
        int a = u, b = v - h0;
        if (adjq(a, b) || deg[a] >= d || deg[HM + b] >= d) continue;
        add_edge(a, b);
    }

    int bestH = 0;
    gE = 0;
    cur_cost = cost();
    if (cur_cost == 0) {
        bestH = hc;
        save_state(ga, gb, &gE);
        if (hc < HM) {
            hc++;
            cur_cost = cost();
        }
    }

    int done = 0;
    const int L = 3000;
    const double T0 = 2.0, TE = 0.1;
    while (!done && elapsed() < budget) {
        save_state(sa, sb, &sE);
        int runBest = cur_cost;
        int grew = 0;
        for (int it = 0; it < L; it++) {
            if ((it & 63) == 0 && elapsed() >= budget) { done = 1; break; }
            double T = T0 * pow(TE / T0, (double)it / L);
            anneal_step(T);
            if (cur_cost == 0) {
                bestH = hc;
                save_state(ga, gb, &gE);
                if (hc >= HM) { done = 1; break; }
                hc++;
                cur_cost = cost();
                grew = 1;
                break;
            }
            if (cur_cost < runBest) {
                runBest = cur_cost;
                save_state(sa, sb, &sE);
            }
        }
        if (!grew && !done && cur_cost != runBest) {
            load_state(sa, sb, sE);
            cur_cost = cost();
        }
    }

    if (bestH == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestH, gE);
    for (int i = 0; i < gE; i++) {
        printf("%d %d\n", ga[i], bestH + gb[i]);
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

def _two_colour(n, edges):
    """Return a 0/1 side label per vertex (bipartition), or None if not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return None
    return col


def _balanced(n, edges):
    """Relabel a bipartite graph so side A is ids 0..h-1 and side B is h..2h-1 (padded to equal size).

    Returns (2h, edges) or None if the graph is not bipartite.
    """
    col = _two_colour(n, edges)
    if col is None:
        return None
    A = [v for v in range(n) if col[v] == 0]
    B = [v for v in range(n) if col[v] == 1]
    h = max(len(A), len(B))
    lab = {}
    for i, v in enumerate(A):
        lab[v] = i
    for i, v in enumerate(B):
        lab[v] = h + i
    out = []
    for u, v in edges:
        a, b = lab[u], lab[v]
        if a >= h:
            a, b = b, a
        out.append((a, b))
    return 2 * h, out


def _extend_spare(n, edges, d, D, deadline):
    """Greedily add fresh vertex pairs while the graph stays valid. Returns (n, edges)."""
    if d < 2:
        return n, edges
    col = _two_colour(n, edges)
    if col is None:
        return n, edges
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    edges = list(edges)
    while time.monotonic() < deadline:
        A_sp = [v for v in range(n) if col[v] == 0 and deg[v] < d]
        B_sp = [v for v in range(n) if col[v] == 1 and deg[v] < d]
        if not A_sp or not B_sp:
            break
        grown = False
        for k in range(d - 1, 0, -1):
            if k > len(A_sp) or k > len(B_sp):
                continue
            a, b = n, n + 1
            cand_new = [(a, b)] + [(a, x) for x in B_sp[:k]] + [(b, y) for y in A_sp[:k]]
            cand = edges + cand_new
            if lib.is_valid(n + 2, cand, d, D):
                edges = cand
                n += 2
                col += [0, 1]
                deg += [0, 0]
                deg[a] = k + 1
                deg[b] = k + 1
                for x in B_sp[:k]:
                    deg[x] += 1
                for y in A_sp[:k]:
                    deg[y] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Group sampling and the search phases.
# ----------------------------------------------------------------------------

K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81, 84, 96, 108, 121,
              128, 162, 243]


def _groups_of_order(N, d):
    """All (m, k2, r) with Z_m x|_r Z_k2 of order exactly N (k2 divides N)."""
    out = []
    for k2 in range(1, N + 1):
        if N % k2 or k2 > 4096:
            continue
        m = N // k2
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    return [g for g in out if g[0] * g[1] >= 2 * d]


def _haar_phase(d, D, rng, state, until):
    """Search Haar graphs of groups of growing order; improves state[0] in place."""
    good = state[0][0] // 2
    N = good + 1
    fails = 0
    while True:
        remaining = until - time.monotonic()
        if remaining < 1.5 or N > 1400:
            break
        grps = _groups_of_order(N, d)
        if not grps:
            N += 1
            continue
        m, k2, r = rng.choice(grps)
        slice_s = min(remaining - 0.5, 4.0)
        try:
            out = lib.run_c(
                HAAR_C_SOURCE,
                [d, D, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 5.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            n, e = 0, []
        if n > state[0][0] and lib.is_valid(n, e, d, D):
            state[0] = (n, e)
            good = n // 2
            N = good + (1 if good >= 480 else max(1, good // 16))
            fails = 0
        else:
            fails += 1
            if fails >= 10 and N > good + 1:
                N = good + 1
                fails = 0


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice(K2_CHOICES)
        m = max(2, -(-target // k2))
        r = 1  # r = 1 is the direct product, always valid
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        return m, k2, r
    return None


def _lift_phase(d, D, rng, state, until):
    """Search bi-Cayley lifts; improves state[0] in place until time `until`."""
    step = 0.08
    while True:
        remaining = until - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 10.0)
        k = rng.choice([1, 1, 2, 2, 3])
        want = state[0][0] * (1.0 + step)
        target = max(2, math.ceil(want / (2 * k)))
        grp = _sample_group(target, rng)
        if grp is None:
            continue
        m, k2, r = grp
        try:
            out = lib.run_c(
                LIFT_C_SOURCE,
                [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 5.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            step = max(0.005, step * 0.7)
            continue
        if n > state[0][0] and lib.is_valid(n, e, d, D):
            state[0] = (n, e)
            step = min(0.4, step * 1.25)
        else:
            step = max(0.005, step * 0.7)


def _repair_phase(d, D, rng, state, deadline):
    """Annealing repair on the general bipartite graph, growing the vertex count."""
    if D < 3 or d < 2 or d > 16:
        return
    rem = deadline - time.monotonic() - 1.0
    if rem < 3.0:
        return
    bal = _balanced(state[0][0], state[0][1])
    if bal is None or bal[0] // 2 > 690:
        return
    out = lib.run_c(
        REPAIR_C_SOURCE,
        [d, D, rng.randrange(1, 10 ** 9), f"{rem:.2f}"],
        stdin_graph=bal,
        timeout=rem + 2.0,
    )
    n, e = lib.parse_graph_text(out)
    if n > state[0][0] and lib.is_valid(n, e, d, D):
        state[0] = (n, e)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    state = [lib.haar_graph(d, range(d))]

    def consider(cand):
        n, e = cand
        if n > state[0][0] and lib.is_valid(n, e, d, D):
            state[0] = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg)
            if D == 3 and lib.is_prime_power(d - 1):
                return state[0]

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return state[0]

    # Phase 1 (bold): Haar graphs of non-abelian / cyclic groups of growing order.
    if D >= 3 and d >= 2:
        try:
            _haar_phase(d, D, rng, state, start + 0.55 * budget)
        except Exception:
            pass

    # Phase 2: bi-Cayley lift search from the current best.
    try:
        _lift_phase(d, D, rng, state, start + 0.8 * budget)
    except Exception:
        pass

    # Phase 3: annealing repair with vertex growth.
    try:
        _repair_phase(d, D, rng, state, deadline)
    except Exception:
        pass

    # Phase 4: spare-degree extension (no-op for regular graphs).
    try:
        best = state[0]
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            state[0] = (n2, e2)
    except Exception:
        pass

    best = state[0]
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
