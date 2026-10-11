import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Phase 1 engine (unchanged from the parent): voltage lifts of semidirect
# products Z_m x| Z_k2 over a base of K A-vertices and K B-vertices, searched by
# simulated annealing with breakout weights and an elite-pool ILS.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Each layer is a permutation, so every vertex has
# degree DEG. Diameter <= D iff BFS of depth D from each block representative
# covers all vertices.
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
# Phase 2 engine (new): grow-and-repair search on regular bipartite graphs.
#
# State: a d-regular bipartite graph with N vertices per side, stored as an
# edge list (EA[e], EB[e]) with local indices, plus adjacency lists.
# Moves: degree-preserving edge switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
# Cost: number of ordered vertex pairs at distance > D, computed by bitset
# BFS from all vertices. A zero-cost state is a valid graph; it is saved and
# then grown by one vertex per side (rewire d edges through the new pair),
# and annealing continues at the larger order.
# Simulated annealing runs in cycles that restart from the best state of the
# current order. Output is the largest zero-cost graph found.
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1400
#define CYC 30000
#define TEMP0 40.0
#define TEMP1 0.5

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

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

static int d_, D_, N, M;
static int *EA, *EB, *adjA, *adjB, *degA, *degB;
static int *snapA, *snapB, *bestA, *bestB;
static int bestN = 0, bestM = 0;
static uint64_t *bufx, *bufy;
static int WMAX;

static inline int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int hasA(int a, int b) {
    const int *nb = adjA + (size_t)a * d_;
    for (int k = 0; k < degA[a]; k++) if (nb[k] == b) return 1;
    return 0;
}

static int hasB(int b, int a) {
    const int *nb = adjB + (size_t)b * d_;
    for (int k = 0; k < degB[b]; k++) if (nb[k] == a) return 1;
    return 0;
}

static void repl(int *list, int deg, int old, int nw) {
    for (int k = 0; k < deg; k++) if (list[k] == old) { list[k] = nw; return; }
}

static void rebuild_adj(void) {
    for (int i = 0; i < N; i++) { degA[i] = 0; degB[i] = 0; }
    for (int e = 0; e < M; e++) {
        int a = EA[e], b = EB[e];
        adjA[(size_t)a * d_ + degA[a]++] = b;
        adjB[(size_t)b * d_ + degB[b]++] = a;
    }
}

/* Ordered pairs at distance > D_, via bitset BFS. Zero iff valid. */
static long long cost_eval(void) {
    int n = 2 * N;
    int W = (n + 63) >> 6;
    uint64_t *cur = bufx, *nxt = bufy;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            if (v < N) {
                const int *nb = adjA + (size_t)v * d_;
                for (int k = 0; k < degA[v]; k++) {
                    int u = N + nb[k];
                    const uint64_t *su = cur + (size_t)u * W;
                    for (int w = 0; w < W; w++) dst[w] |= su[w];
                }
            } else {
                int j = v - N;
                const int *nb = adjB + (size_t)j * d_;
                for (int k = 0; k < degB[j]; k++) {
                    int u = nb[k];
                    const uint64_t *su = cur + (size_t)u * W;
                    for (int w = 0; w < W; w++) dst[w] |= su[w];
                }
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *row = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc64(row[w]);
        total += n - c;
    }
    return total;
}

/* Switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Returns 0 if not allowed.
   Applying it twice in a row restores the original state. */
static int apply_switch(int e1, int e2) {
    int a1 = EA[e1], b1 = EB[e1], a2 = EA[e2], b2 = EB[e2];
    if (a1 == a2 || b1 == b2) return 0;
    if (hasA(a1, b2) || hasA(a2, b1)) return 0;
    repl(adjA + (size_t)a1 * d_, degA[a1], b1, b2);
    repl(adjB + (size_t)b1 * d_, degB[b1], a1, a2);
    repl(adjA + (size_t)a2 * d_, degA[a2], b2, b1);
    repl(adjB + (size_t)b2 * d_, degB[b2], a2, a1);
    EA[e1] = a1; EB[e1] = b2;
    EA[e2] = a2; EB[e2] = b1;
    return 1;
}

/* Add one vertex per side. Each of d steps moves an old edge (a1,b1) to
   (a*,b1) and adds (a1,b*), so the old degrees are kept and the new pair
   reaches degree d. */
static void grow_one(void) {
    int as = N, bs = N;
    int mold = M;
    N++;
    degA[as] = 0;
    degB[bs] = 0;
    for (int s = 0; s < d_; s++) {
        int e, a1, b1;
        for (;;) {
            e = rnd_int(mold);
            a1 = EA[e];
            b1 = EB[e];
            if (a1 == as) continue;
            if (hasA(as, b1) || hasB(bs, a1)) continue;
            break;
        }
        repl(adjA + (size_t)a1 * d_, degA[a1], b1, bs);
        repl(adjB + (size_t)b1 * d_, degB[b1], a1, as);
        adjA[(size_t)as * d_ + degA[as]++] = b1;
        adjB[(size_t)bs * d_ + degB[bs]++] = a1;
        EA[e] = as;
        EB[e] = b1;
        EA[M] = a1;
        EB[M] = bs;
        M++;
    }
}

static void snapshot(void) {
    memcpy(snapA, EA, sizeof(int) * (size_t)M);
    memcpy(snapB, EB, sizeof(int) * (size_t)M);
}

static void restore_snap(void) {
    memcpy(EA, snapA, sizeof(int) * (size_t)M);
    memcpy(EB, snapB, sizeof(int) * (size_t)M);
    rebuild_adj();
}

static void save_best(void) {
    bestN = N;
    bestM = M;
    memcpy(bestA, EA, sizeof(int) * (size_t)M);
    memcpy(bestB, EB, sizeof(int) * (size_t)M);
}

/* Reads "n m" and edges; accepts only a d-regular bipartite graph with equal sides.
   Sets N, M, EA, EB on success. Returns 0 otherwise (caller falls back to K_{d,d}). */
static int load_graph(void) {
    long long n = 0, m = 0;
    if (scanf("%lld %lld", &n, &m) != 2) return 0;
    if (n <= 0 || m <= 0) return 0;
    if (n % 2 != 0 || n > 2LL * (NMAX - 3)) return 0;
    if (m * 2 != n * (long long)d_) return 0;
    int nn = (int)n, mm = (int)m;
    int *eu = malloc(sizeof(int) * (size_t)mm);
    int *ev = malloc(sizeof(int) * (size_t)mm);
    int *gdeg = calloc((size_t)nn, sizeof(int));
    int *gadj = malloc(sizeof(int) * (size_t)nn * d_);
    int *col = malloc(sizeof(int) * (size_t)nn);
    int *stk = malloc(sizeof(int) * (size_t)nn);
    int *idx = malloc(sizeof(int) * (size_t)nn);
    int ok = 1;
    for (int i = 0; i < mm && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= nn || v >= nn || u == v) { ok = 0; break; }
        if (gdeg[u] >= d_ || gdeg[v] >= d_) { ok = 0; break; }
        gadj[(size_t)u * d_ + gdeg[u]++] = v;
        gadj[(size_t)v * d_ + gdeg[v]++] = u;
        eu[i] = u;
        ev[i] = v;
    }
    for (int v = 0; ok && v < nn; v++) if (gdeg[v] != d_) ok = 0;
    for (int v = 0; v < nn; v++) col[v] = -1;
    for (int s = 0; ok && s < nn; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0 && ok) {
            int v = stk[--sp];
            for (int k = 0; k < d_; k++) {
                int u = gadj[(size_t)v * d_ + k];
                if (col[u] < 0) {
                    col[u] = 1 - col[v];
                    stk[sp++] = u;
                } else if (col[u] == col[v]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    int ca = 0, cb = 0;
    for (int v = 0; ok && v < nn; v++) {
        if (col[v] == 0) idx[v] = ca++;
        else idx[v] = cb++;
    }
    if (ok && (ca != cb || ca != nn / 2)) ok = 0;
    if (ok) {
        int *TA = malloc(sizeof(int) * (size_t)mm);
        int *TB = malloc(sizeof(int) * (size_t)mm);
        for (int i = 0; i < mm; i++) {
            int u = eu[i], v = ev[i];
            int a = (col[u] == 0) ? u : v;
            int b = (col[u] == 0) ? v : u;
            TA[i] = idx[a];
            TB[i] = idx[b];
        }
        memcpy(EA, TA, sizeof(int) * (size_t)mm);
        memcpy(EB, TB, sizeof(int) * (size_t)mm);
        N = nn / 2;
        M = mm;
        free(TA);
        free(TB);
    }
    free(eu); free(ev); free(gdeg); free(gadj); free(col); free(stk); free(idx);
    return ok;
}

int main(int argc, char **argv) {
    timespec_get(&T0, TIME_UTC);
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (d_ < 1 || D_ < 1 || d_ > 64) {
        printf("0 0\n");
        return 0;
    }
    WMAX = (2 * NMAX + 63) / 64;
    EA = malloc(sizeof(int) * (size_t)NMAX * d_);
    EB = malloc(sizeof(int) * (size_t)NMAX * d_);
    adjA = malloc(sizeof(int) * (size_t)NMAX * d_);
    adjB = malloc(sizeof(int) * (size_t)NMAX * d_);
    degA = calloc((size_t)NMAX, sizeof(int));
    degB = calloc((size_t)NMAX, sizeof(int));
    snapA = malloc(sizeof(int) * (size_t)NMAX * d_);
    snapB = malloc(sizeof(int) * (size_t)NMAX * d_);
    bestA = malloc(sizeof(int) * (size_t)NMAX * d_);
    bestB = malloc(sizeof(int) * (size_t)NMAX * d_);
    bufx = malloc(sizeof(uint64_t) * (size_t)(2 * NMAX) * WMAX);
    bufy = malloc(sizeof(uint64_t) * (size_t)(2 * NMAX) * WMAX);

    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    if (!load_graph()) {
        N = d_;
        M = d_ * d_;
        for (int a = 0; a < N; a++)
            for (int b = 0; b < N; b++) {
                EA[a * N + b] = a;
                EB[a * N + b] = b;
            }
    }
    rebuild_adj();

    long long cur = cost_eval();
    snapshot();
    long long snapc = cur;
    int cyc = 0;
    if (cur == 0) save_best();

    while (elapsed() < DEADLINE) {
        if (cur == 0) {
            save_best();
            if (N + 2 >= NMAX) break;
            grow_one();
            cur = cost_eval();
            snapshot();
            snapc = cur;
            cyc = 0;
            continue;
        }
        double frac = (double)cyc / CYC;
        double temp = TEMP0 * pow(TEMP1 / TEMP0, frac);
        int e1 = rnd_int(M), e2 = rnd_int(M);
        cyc++;
        if (e1 != e2 && apply_switch(e1, e2)) {
            long long c2 = cost_eval();
            if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
                cur = c2;
                if (cur < snapc) {
                    snapc = cur;
                    snapshot();
                }
            } else {
                apply_switch(e1, e2);
            }
        }
        if (cyc >= CYC) {
            restore_snap();
            cur = snapc;
            cyc = 0;
        }
    }
    if (cur == 0) save_best();

    if (bestN > 0) {
        printf("%d %d\n", 2 * bestN, bestM);
        for (int e = 0; e < bestM; e++)
            printf("%d %d\n", bestA[e], bestN + bestB[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph for degree d = q + 2 with q a prime power >= 3; diameter 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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


def _is_regular(n, edges, d):
    """True if the graph has an even order and every vertex has degree exactly d."""
    if n <= 0 or n % 2:
        return False
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# Driver: baselines, then phase 1 (voltage-lift annealer), then phase 2
# (grow-and-repair on the best regular graph found so far).
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
            return True
        return False

    if D >= 3:
        for builder in (_best_pg, _araujo):
            try:
                g = builder(d)
                if g is not None:
                    consider(g[0], g[1])
            except Exception:
                pass

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Leave margin for compilation, validation and parsing.
    t_end = start + 0.86 * time_limit - 1.0

    # Phase 1: voltage-lift annealer (proven to reach the record for d=6, D=5).
    b1 = 0.5 * (t_end - time.monotonic())
    if b1 >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{b1:.2f}", best_n],
                            timeout=b1 + 4.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Phase 2: grow the best regular graph by one vertex per side and repair by
    # edge switches. Starts from K_{d,d} if the best graph is not regular.
    b2 = t_end - time.monotonic()
    if b2 >= 2.0:
        seed_graph = best if _is_regular(best[0], best[1], d) else None
        try:
            out = lib.run_c(C_GROW, [d, D, seed, f"{b2:.2f}"],
                            stdin_graph=seed_graph, timeout=b2 + 4.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
