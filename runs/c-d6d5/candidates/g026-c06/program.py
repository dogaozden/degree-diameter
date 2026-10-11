import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage A: voltage lifts of semidirect products Z_m x| Z_k over a small base,
# searched by simulated annealing with breakout weights and iterated local
# search. This is the parent's engine, unchanged. It supplies a structured
# start graph (the record family for d=6, D=5).
# ----------------------------------------------------------------------------

LIFT_SOURCE = r"""
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
# Stage B: unstructured edge-swap annealing on bipartite d-regular graphs.
#
# Start: the graph passed on stdin (if it is d-regular with parts [0,n/2) and
# [n/2,n)), otherwise a random d-regular bipartite graph on 2*htarget vertices.
# Moves: 2-switches (a1-b1, a2-b2) -> (a1-b2, a2-b1), which keep the bipartition
# and every degree. Cost: number of ordered vertex pairs at distance > D,
# computed by bitset BFS. When cost reaches 0 the graph is saved, then grown by
# one vertex on each side (wired in by degree-preserving edge splices), and
# annealing continues. The last saved valid graph is printed.
# ----------------------------------------------------------------------------

EDGE_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CYCLE 8.0
#define TEMP_HI 3.0
#define TEMP_LO 0.15
#define BATCH 200

static struct timespec TS0;
static double DEADLINE;
static uint64_t rs[2];
static int DEG, DIAM;
static int H, N, W, M, CAP;
static int *EA = NULL, *EB = NULL;
static int *nb = NULL, *ncnt = NULL;
static uint64_t *adj = NULL, *R1 = NULL, *R2 = NULL;
static int bestM = 0, bestH = 0;
static int *bestA = NULL, *bestB = NULL;

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
    return (double)(ts.tv_sec - TS0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - TS0.tv_nsec);
}

static int cmp_ll(const void *a, const void *b) {
    long long x = *(const long long *)a, y = *(const long long *)b;
    return (x > y) - (x < y);
}

static inline int has_bit(int u, int v) {
    return (int)((adj[(size_t)u * W + (size_t)(v >> 6)] >> (v & 63)) & 1ULL);
}
static inline void set_bit(int u, int v) {
    adj[(size_t)u * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
}
static inline void clr_bit(int u, int v) {
    adj[(size_t)u * W + (size_t)(v >> 6)] &= ~(1ULL << (v & 63));
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void free_all(void) {
    free(adj); free(R1); free(R2); free(nb); free(ncnt);
    adj = R1 = R2 = NULL;
    nb = NULL;
    ncnt = NULL;
}

static void alloc_H(int h) {
    H = h;
    N = 2 * h;
    W = (N + 63) / 64;
    adj = calloc((size_t)N * W, sizeof(uint64_t));
    R1 = malloc(sizeof(uint64_t) * (size_t)N * W);
    R2 = malloc(sizeof(uint64_t) * (size_t)N * W);
    nb = malloc(sizeof(int) * (size_t)N * DEG);
    ncnt = malloc(sizeof(int) * (size_t)N);
    CAP = DEG * (h + 3);
    EA = realloc(EA, sizeof(int) * (size_t)CAP);
    EB = realloc(EB, sizeof(int) * (size_t)CAP);
}

static void set_bits(void) {
    memset(adj, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int e = 0; e < M; e++) {
        set_bit(EA[e], EB[e]);
        set_bit(EB[e], EA[e]);
    }
}

/* Re-index B side from [H, 2H) to [nh, 2nh) keeping the edge list. */
static void resize_H(int nh) {
    for (int e = 0; e < M; e++)
        if (EB[e] >= H) EB[e] += nh - H;
    free_all();
    alloc_H(nh);
    set_bits();
}

static long long eval_cost(void) {
    memset(ncnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < M; e++) {
        int a = EA[e], b = EB[e];
        nb[(size_t)a * DEG + ncnt[a]++] = b;
        nb[(size_t)b * DEG + ncnt[b]++] = a;
    }
    uint64_t *cur = R1, *nxt = R2;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
            for (int j = 0; j < ncnt[v]; j++) {
                const uint64_t *t = cur + (size_t)nb[(size_t)v * DEG + j] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(cur[(size_t)v * W + w]);
        cost += N - c;
    }
    return cost;
}

static void add_edge(int a, int b) {
    EA[M] = a;
    EB[M] = b;
    M++;
    set_bit(a, b);
    set_bit(b, a);
}

static int random_regular(int h) {
    if (adj) free_all();
    M = 0;
    alloc_H(h);
    int *p = malloc(sizeof(int) * (size_t)h);
    int ok_all = 1;
    for (int l = 0; l < DEG && ok_all; l++) {
        int ok = 0;
        for (int tr = 0; tr < 5000 && !ok; tr++) {
            for (int i = 0; i < h; i++) p[i] = i;
            for (int i = h - 1; i > 0; i--) {
                int j = rnd_int(i + 1);
                int t = p[i]; p[i] = p[j]; p[j] = t;
            }
            ok = 1;
            for (int i = 0; i < h; i++)
                if (has_bit(i, h + p[i])) { ok = 0; break; }
        }
        if (!ok) ok_all = 0;
        else
            for (int i = 0; i < h; i++) add_edge(i, h + p[i]);
    }
    free(p);
    return ok_all;
}

/* Grow a d-regular graph by one vertex per side, keeping it d-regular.
   Each of the DEG steps splices an old edge (a,b) into (x,b) and (a,y). */
static int expand_pair(void) {
    int oldH = H;
    resize_H(oldH + 1);
    int x = oldH;
    int y = 2 * H - 1;
    for (int t = 0; t < DEG; t++) {
        int found = 0;
        for (int tr = 0; tr < 200000 && !found; tr++) {
            int e = rnd_int(M);
            int a = EA[e], b = EB[e];
            if (a >= oldH) continue;
            if (b < H || b >= H + oldH) continue;
            if (has_bit(a, y) || has_bit(x, b)) continue;
            found = 1;
            clr_bit(a, b);
            clr_bit(b, a);
            set_bit(x, b);
            set_bit(b, x);
            EA[e] = x;
            add_edge(a, y);
        }
        if (!found) return 0;
    }
    return 1;
}

static void sa_step(double temp, long long *cost) {
    int e1 = rnd_int(M), e2 = rnd_int(M);
    if (e1 == e2) return;
    int a1 = EA[e1], b1 = EB[e1], a2 = EA[e2], b2 = EB[e2];
    if (a1 == a2 || b1 == b2) return;
    if (has_bit(a1, b2) || has_bit(a2, b1)) return;
    clr_bit(a1, b1); clr_bit(b1, a1);
    clr_bit(a2, b2); clr_bit(b2, a2);
    set_bit(a1, b2); set_bit(b2, a1);
    set_bit(a2, b1); set_bit(b1, a2);
    EB[e1] = b2;
    EB[e2] = b1;
    long long c2 = eval_cost();
    long long dl = c2 - *cost;
    if (dl <= 0 || rnd_unit() < exp(-(double)dl / temp)) {
        *cost = c2;
        return;
    }
    clr_bit(a1, b2); clr_bit(b2, a1);
    clr_bit(a2, b1); clr_bit(b1, a2);
    set_bit(a1, b1); set_bit(b1, a1);
    set_bit(a2, b2); set_bit(b2, a2);
    EB[e1] = b1;
    EB[e2] = b2;
}

static void save_best(void) {
    free(bestA);
    free(bestB);
    bestA = malloc(sizeof(int) * (size_t)M);
    bestB = malloc(sizeof(int) * (size_t)M);
    memcpy(bestA, EA, sizeof(int) * (size_t)M);
    memcpy(bestB, EB, sizeof(int) * (size_t)M);
    bestM = M;
    bestH = H;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [htarget]\n");
        return 1;
    }
    timespec_get(&TS0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int htarget = argc > 5 ? atoi(argv[5]) : 2;
    if (DEG < 2 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 977ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n_in = 0, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2) { n_in = 0; m_in = 0; }
    int loaded = 0;
    if (n_in > 0 && n_in % 2 == 0 && m_in > 0 && m_in == DEG * (n_in / 2)) {
        int h = n_in / 2;
        int *ia = malloc(sizeof(int) * (size_t)m_in);
        int *ib = malloc(sizeof(int) * (size_t)m_in);
        long long *keys = malloc(sizeof(long long) * (size_t)m_in);
        int *dg = calloc((size_t)n_in, sizeof(int));
        int good = 1;
        for (int i = 0; i < m_in && good; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { good = 0; break; }
            if (u > v) { int t = u; u = v; v = t; }
            if (!(u >= 0 && u < h && v >= h && v < n_in)) { good = 0; break; }
            ia[i] = u;
            ib[i] = v;
            dg[u]++;
            dg[v]++;
            keys[i] = (long long)u * n_in + v;
        }
        for (int v = 0; good && v < n_in; v++)
            if (dg[v] != DEG) good = 0;
        if (good) {
            qsort(keys, (size_t)m_in, sizeof(long long), cmp_ll);
            for (int i = 1; i < m_in; i++)
                if (keys[i] == keys[i - 1]) { good = 0; break; }
        }
        if (good) {
            M = m_in;
            alloc_H(h);
            memcpy(EA, ia, sizeof(int) * (size_t)m_in);
            memcpy(EB, ib, sizeof(int) * (size_t)m_in);
            set_bits();
            loaded = 1;
        }
        free(ia); free(ib); free(keys); free(dg);
    }
    if (!loaded) {
        if (htarget < 2) htarget = 2;
        if (!random_regular(htarget)) {
            printf("0 0\n");
            return 0;
        }
    }

    long long cost = eval_cost();
    double cyc = elapsed();
    while (elapsed() < DEADLINE) {
        double now = elapsed();
        if (now - cyc >= CYCLE) cyc = now;
        double frac = (now - cyc) / CYCLE;
        double temp = TEMP_HI * pow(TEMP_LO / TEMP_HI, frac);
        for (int s = 0; s < BATCH && cost > 0; s++) sa_step(temp, &cost);
        if (cost == 0) {
            save_best();
            if (elapsed() >= DEADLINE) break;
            if (!expand_pair()) {
                if (!random_regular(H)) break;
            }
            cost = eval_cost();
            cyc = elapsed();
        }
    }

    if (bestM > 0) {
        printf("%d %d\n", 2 * bestH, bestM);
        for (int i = 0; i < bestM; i++)
            printf("%d %d\n", bestA[i], bestB[i]);
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
# Driver: baselines, then stage A (lift engine) and stage B (edge annealing
# that grows a regular bipartite graph from the stage A result).
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

    if best_n >= lib.moore_bound(d, D):
        return best

    def left():
        return 0.85 * time_limit - (time.monotonic() - start) - 2.0

    # Stage A: structured lift search (short budget; provides the start graph).
    budget_a = 0.3 * left()
    if budget_a >= 2.0:
        try:
            out = lib.run_c(LIFT_SOURCE, [d, D, seed, f"{budget_a:.2f}"],
                            timeout=budget_a + 10.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    # Stage B: unstructured edge-swap annealing that grows the best regular graph.
    budget_b = left()
    if budget_b >= 2.0:
        try:
            out = lib.run_c(EDGE_SOURCE, [d, D, seed, f"{budget_b:.2f}", best_n // 2 + 1],
                            stdin_graph=best, timeout=budget_b + 15.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
