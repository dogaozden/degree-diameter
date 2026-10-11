import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 C engine (unchanged from the parent): voltage lifts of semidirect
# products Z_m x| Z_k2 over a base of K A-vertices and K B-vertices, searched
# by simulated annealing with breakout weights and an elite pool (ILS).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 6000
#define ILS_ITERS 3000
#define POOLMAX 48
#define POOLP 0.6
#define BRK 150

static uint64_t rs[2];
static struct timespec T0;

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

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DEG, DIAM, K, K2, M, G, T, MAXT;
static int R;
static int *Rpow;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bestJ, *bestS;
static int curstamp;
static double DEADLINE;
static int best_n, best_m;
static int *best_e = NULL;

static long long *wt = NULL;
static long long *unc = NULL;
static long long wsum_w = 0;
static long long last_w = 0;

typedef struct {
    int K, K2, M, R;
    long long cost;
    int *J, *S;
} Cfg;

static Cfg pool[POOLMAX];
static int npool = 0;

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

static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static long long eval_cost(void) {
    int N = 2 * K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
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
                const int *au = adj + (size_t)f[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        h[nsz++] = v;
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        unc[r] = N - count;
        total += N - count;
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void alloc_config(void) {
    int N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    curstamp = 0;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx); free(Rpow);
    free(wt); free(unc);
    dI = dJ = dS = bestJ = bestS = perm = adj = cnt = stamp = fr = nx = Rpow = NULL;
    wt = unc = NULL;
}

static void setup_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r; G = m * c2;
    alloc_config();
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int b = 0; b < 2 * K; b++) wt[b] = 1;
    wsum_w = 2 * K;
}

static void emit(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    }
    best_m = m;
    best_n = 2 * K * G;
}

static void random_init(void) {
    int p[8];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

static void perturb(int nmoves) {
    for (int s = 0; s < nmoves; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
        } else {
            int t = rnd_int(T);
            dS[t] = rnd_int(G);
            build_perm(t);
        }
    }
}

static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost;
    long long wcur = last_w;
    long long prevc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost < BIGC && cost >= prevc) {
                eval_cost();
                for (int r = 0; r < 2 * K; r++)
                    if (unc[r] > 0) { wt[r]++; wsum_w++; }
                wcur = 0;
                for (int r = 0; r < 2 * K; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double sc = (double)wsum_w / (2.0 * K);
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * sc;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = rnd_int(T);
            int olds = dS[t];
            int news = rnd_int(G);
            if (news == olds) continue;
            dS[t] = news;
            build_perm(t);
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                dS[t] = olds;
                build_perm(t);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bestS, dS, sizeof(int) * (size_t)T);
        }
    }
    return bestc;
}

static void finish_run(long long bc) {
    if (bc == 0) {
        memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
        memcpy(dS, bestS, sizeof(int) * (size_t)T);
        for (int t = 0; t < T; t++) build_perm(t);
        if (2 * K * G > best_n) emit();
    }
}

static void pool_add(long long cost, const int *J, const int *S) {
    if (cost <= 0 || cost >= BIGC) return;
    int slot;
    if (npool < POOLMAX) {
        slot = npool++;
    } else {
        slot = 0;
        for (int i = 1; i < POOLMAX; i++)
            if (pool[i].cost > pool[slot].cost) slot = i;
        if (pool[slot].cost <= cost) return;
    }
    Cfg *c = &pool[slot];
    c->K = K; c->K2 = K2; c->M = M; c->R = R; c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * pool[i].K2 * pool[i].M;
        if (nn > best_n) cand[nc++] = i;
    }
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    best_n = start_n;
    best_m = 0;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    MAXT = 3 * DEG;
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].S = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = BIGC;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[5] = {1, 1, 2, 2, 3};
    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            Cfg c = pool[pi];
            setup_group(c.K, c.K2, c.M, c.R);
            memcpy(dJ, c.J, sizeof(int) * (size_t)T);
            memcpy(dS, c.S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            free_config();
            continue;
        }

        int k = kc[rnd_int(5)];
        int gmin = best_n / (2 * k) + 1;
        int spread = gmin / 6 + 2;
        int g = gmin + rnd_int(spread);
        if (g < 2) g = 2;
        int opts[12], no = 0;
        for (int c = 1; c <= 12; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        int c2 = opts[rnd_int(no)];
        int m = g / c2, r = 1;
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
                m = g;
                r = 1;
            }
        }
        setup_group(k, c2, m, r);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
        free_config();
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
# Stage 2 C engine (new): unstructured repair-and-grow search.
#
# Input: a d-regular bipartite graph that is valid for diameter D (stdin).
# Loop: add one A-vertex and one B-vertex by removing a matching of d edges
# and reconnecting its endpoints to the two new vertices. This keeps every
# degree equal to d. Then anneal over degree-preserving double edge swaps
# (a1-b1, a2-b2 -> a1-b2, a2-b1) to drive the number of bad ordered pairs
# to zero. On success the graph is saved as the new base. On failure the
# base is restored and a new random grow is tried.
#
# Distances are computed with bitsets: reach_t[v] is the set of vertices
# within distance t of v, computed for all v at once. Cost = sum over v of
# (n - |reach_D[v]|), so cost 0 means diameter <= D.
# ----------------------------------------------------------------------------

REPAIR_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CAP 4096
#define MAXDEG 32
#define MAXE (CAP * 16)
#define WMAX (CAP / 64)
#define ITERS 20000
#define TS 6.0
#define TE 0.4

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM, NV, NE;
static int ea[MAXE], eb[MAXE];
static int bea[MAXE], beb[MAXE];
static int bNV, bNE;
static unsigned char adjm[CAP * CAP];
static int adjl[CAP * MAXDEG];
static int cntv[CAP];
static uint64_t bufA[CAP * WMAX], bufB[CAP * WMAX];
static int ord[MAXE];
static int tmpcol[CAP];
static unsigned char usedA[CAP], usedB[CAP];

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

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Set edge i to (ea[i], nbi) and edge j to (ea[j], nbj), keeping adjm in sync. */
static void set_pair(int i, int j, int nbi, int nbj) {
    int a1 = ea[i], a2 = ea[j];
    adjm[a1 * CAP + eb[i]] = 0;
    adjm[a2 * CAP + eb[j]] = 0;
    eb[i] = nbi;
    eb[j] = nbj;
    adjm[a1 * CAP + nbi] = 1;
    adjm[a2 * CAP + nbj] = 1;
}

/* Number of bad ordered pairs (u, w) with dist(u, w) > DIAM. Zero iff valid. */
static long long eval_cost(void) {
    int n = NV, W = (n + 63) / 64;
    for (int v = 0; v < n; v++) cntv[v] = 0;
    for (int e = 0; e < NE; e++) {
        int a = ea[e], b = eb[e];
        adjl[a * DEG + cntv[a]++] = b;
        adjl[b * DEG + cntv[b]++] = a;
    }
    uint64_t *c = bufA, *x = bufB;
    memset(c, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++)
        c[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = x + (size_t)v * W;
            const uint64_t *src = c + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int k = 0; k < DEG; k++) {
                const uint64_t *s2 = c + (size_t)adjl[v * DEG + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = c; c = x; x = t;
    }
    long long cost = 0;
    for (int v = 0; v < n; v++) {
        int cb = 0;
        const uint64_t *row = c + (size_t)v * W;
        for (int w = 0; w < W; w++) cb += pc64(row[w]);
        cost += n - cb;
    }
    return cost;
}

/* Add one A-vertex and one B-vertex, keeping the graph DEG-regular.
   Returns 0 (and changes nothing) if no matching of size DEG exists. */
static int grow_once(void) {
    if (NV + 2 > CAP) return 0;
    if (NE < DEG) return 0;
    for (int e = 0; e < NE; e++) ord[e] = e;
    for (int i = NE - 1; i > 0; i--) {
        int j = rnd_int(i + 1);
        int t = ord[i]; ord[i] = ord[j]; ord[j] = t;
    }
    memset(usedA, 0, (size_t)NV);
    memset(usedB, 0, (size_t)NV);
    int pick[MAXDEG], np = 0;
    for (int k = 0; k < NE && np < DEG; k++) {
        int e = ord[k];
        int a = ea[e], b = eb[e];
        if (!usedA[a] && !usedB[b]) {
            usedA[a] = 1;
            usedB[b] = 1;
            pick[np++] = e;
        }
    }
    if (np < DEG) return 0;

    int La[MAXDEG], Lb[MAXDEG];
    for (int k = 0; k < DEG; k++) {
        La[k] = ea[pick[k]];
        Lb[k] = eb[pick[k]];
    }
    /* Remove picked edges: sort indices descending, then swap-remove. */
    for (int i = 1; i < np; i++) {
        int x = pick[i];
        int j = i - 1;
        while (j >= 0 && pick[j] < x) { pick[j + 1] = pick[j]; j--; }
        pick[j + 1] = x;
    }
    for (int k = 0; k < np; k++) {
        int idx = pick[k];
        adjm[ea[idx] * CAP + eb[idx]] = 0;
        ea[idx] = ea[NE - 1];
        eb[idx] = eb[NE - 1];
        NE--;
    }
    int nA = NV, nB = NV + 1;
    for (int k = 0; k < DEG; k++) {
        ea[NE] = La[k]; eb[NE] = nB; adjm[La[k] * CAP + nB] = 1; NE++;
        ea[NE] = nA; eb[NE] = Lb[k]; adjm[nA * CAP + Lb[k]] = 1; NE++;
    }
    NV += 2;
    return 1;
}

static void save_base(void) {
    memcpy(bea, ea, sizeof(int) * (size_t)NE);
    memcpy(beb, eb, sizeof(int) * (size_t)NE);
    bNV = NV;
    bNE = NE;
}

static void restore_base(void) {
    for (int e = 0; e < NE; e++) adjm[ea[e] * CAP + eb[e]] = 0;
    NV = bNV;
    NE = bNE;
    memcpy(ea, bea, sizeof(int) * (size_t)NE);
    memcpy(eb, beb, sizeof(int) * (size_t)NE);
    for (int e = 0; e < NE; e++) adjm[ea[e] * CAP + eb[e]] = 1;
}

/* Annealing over double edge swaps until the cost is 0. Returns 1 on success. */
static int sa_to_zero(long long iters, double Ts, double Te) {
    long long cost = eval_cost();
    double lr = log(Te / Ts);
    for (long long it = 0; it < iters && cost > 0; it++) {
        if (elapsed() > DEADLINE) break;
        double T = Ts * exp(lr * (double)it / (double)iters);
        int i = rnd_int(NE), j = rnd_int(NE);
        if (i == j) continue;
        int b1 = eb[i], b2 = eb[j];
        if (adjm[ea[i] * CAP + b2] || adjm[ea[j] * CAP + b1]) continue;
        set_pair(i, j, b2, b1);
        long long nc = eval_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            set_pair(i, j, b1, b2);
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    uint64_t sm = sd * 0x9E3779B97F4A7C15ULL + 777ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 2 || n0 > CAP - 2 || m0 < 1 || m0 > MAXE) {
        printf("0 0\n");
        return 0;
    }
    static int ru[MAXE], rv[MAXE];
    static int dg[CAP];
    static int fillc[CAP];
    static int q[CAP];
    for (int e = 0; e < m0; e++) {
        if (scanf("%d %d", &ru[e], &rv[e]) != 2) { printf("0 0\n"); return 0; }
        if (ru[e] < 0 || ru[e] >= n0 || rv[e] < 0 || rv[e] >= n0 || ru[e] == rv[e]) {
            printf("0 0\n");
            return 0;
        }
        dg[ru[e]]++;
        dg[rv[e]]++;
    }
    for (int v = 0; v < n0; v++)
        if (dg[v] != DEG) { printf("0 0\n"); return 0; }
    if (2 * m0 != n0 * DEG) { printf("0 0\n"); return 0; }

    for (int e = 0; e < m0; e++) {
        int a = ru[e], b = rv[e];
        adjl[a * DEG + fillc[a]++] = b;
        adjl[b * DEG + fillc[b]++] = a;
    }
    for (int v = 0; v < n0; v++) tmpcol[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (tmpcol[s] >= 0) continue;
        tmpcol[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int k = 0; k < DEG; k++) {
                int w = adjl[u * DEG + k];
                if (tmpcol[w] < 0) {
                    tmpcol[w] = 1 - tmpcol[u];
                    q[qt++] = w;
                }
            }
        }
    }

    NV = n0;
    NE = 0;
    for (int e = 0; e < m0; e++) {
        int u = ru[e], v = rv[e];
        if (tmpcol[u] == tmpcol[v]) { printf("0 0\n"); return 0; }
        int a = (tmpcol[u] == 0) ? u : v;
        int b = (a == u) ? v : u;
        if (adjm[a * CAP + b]) { printf("0 0\n"); return 0; }
        adjm[a * CAP + b] = 1;
        ea[NE] = a;
        eb[NE] = b;
        NE++;
    }

    if (eval_cost() != 0) {
        if (!sa_to_zero(ITERS, TS, TE)) {
            printf("0 0\n");
            return 0;
        }
    }
    save_base();

    while (elapsed() < DEADLINE) {
        if (!grow_once()) break;
        if (sa_to_zero(ITERS, TS, TE)) {
            save_base();
        } else {
            restore_base();
        }
    }

    printf("%d %d\n", bNV, bNE);
    for (int e = 0; e < bNE; e++)
        printf("%d %d\n", bea[e], beb[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent).
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
# Driver: baselines, then the lift annealer, then the repair-and-grow search
# on the best graph found so far. Every candidate is checked with lib.is_valid.
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

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Budget: two C compiles (cold cache) plus parsing and validation, then
    # split the rest between the lift annealer and the repair-and-grow search.
    avail = 0.92 * time_limit - (time.monotonic() - start) - 3.0
    if avail >= 2.0:
        t_lift = 0.4 * avail
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{t_lift:.2f}", best_n],
                            timeout=t_lift + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

        # Repair stage: start from the best valid graph (it is d-regular for
        # the lift and K_{d,d} cases; the C engine rejects any other input).
        t_rep = 0.92 * time_limit - (time.monotonic() - start) - 2.5
        if t_rep >= 1.0:
            try:
                out = lib.run_c(REPAIR_SOURCE, [d, D, seed, f"{t_rep:.2f}"],
                                stdin_graph=best, timeout=t_rep + 8.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
