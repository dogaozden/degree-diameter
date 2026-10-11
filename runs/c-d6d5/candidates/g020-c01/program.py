import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 C engine (unchanged from the parent): voltage lifts of semidirect
# products Z_m x| Z_k2 over a base of K A-vertices and K B-vertices, searched by
# simulated annealing with breakout weights and an elite pool (ILS).
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Each layer is a permutation, so every vertex
# has degree DEG. Left multiplication is an automorphism, so diameter <= D
# iff BFS of depth D from each of the 2K block representatives covers all.
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
# Stage 2 C engine (new): free-form growth by edge switching on the full graph.
#
# Starts from a valid d-regular bipartite graph read from stdin. Repeatedly:
#   1. Grow by two vertices (one per side) using degree-preserving 2-switches
#      that move edges onto the new vertices, so the graph stays d-regular.
#   2. Simulated annealing on random 2-switches (both sides keep degrees),
#      with cost = number of ordered vertex pairs at distance > D, computed
#      exactly by bitset BFS.
#   3. On reaching cost 0, the new graph becomes the backup. On failure the
#      backup (last valid graph) is restored and growth is retried.
# The output is always the last valid backup, so it never gets worse than the
# input. Output "0 0" if the input is not a valid d-regular bipartite graph.
# ----------------------------------------------------------------------------

ANNEAL_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NCAP 4096
#define WCAP 64
#define DMAX 16
#define ATT_EVALS 8000
#define T_HI 4.0
#define T_LO 0.3

static int DEG, DIAM;
static double DEADLINE;
static struct timespec T0;
static uint64_t rs[2];

static int n_cur, nA;
static int dg[NCAP];
static int col[NCAP];
static int nb[NCAP * DMAX];
static int listA[NCAP];
static int backup_n, backup_nA;
static int backup_nb[NCAP * DMAX];
static uint64_t reachA[NCAP * WCAP];
static uint64_t reachB[NCAP * WCAP];
static int queue_[NCAP];

typedef struct { int a1, i, b1, a2, j, b2, k, l; } Mv;

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

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int find_slot(int u, int v) {
    const int *p = nb + (size_t)u * DMAX;
    for (int i = 0; i < dg[u]; i++)
        if (p[i] == v) return i;
    return -1;
}

/* Number of ordered pairs (u,v), u != v, at distance > DIAM. */
static long long eval_cost(void) {
    const int n = n_cur;
    const int W = (n + 63) / 64;
    memset(reachA, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++)
        reachA[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    uint64_t *cur = reachA, *nxt = reachB;
    for (int lvl = 0; lvl < DIAM; lvl++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *out = nxt + (size_t)v * W;
            const uint64_t *in = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) out[w] = in[w];
            for (int i = 0; i < dg[v]; i++) {
                size_t u = (size_t)nb[(size_t)v * DMAX + i];
                const uint64_t *src = cur + u * (size_t)W;
                for (int w = 0; w < W; w++) out[w] |= src[w];
            }
            for (int w = 0; w < W; w++)
                if (out[w] != in[w]) { changed = 1; break; }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long total = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *r = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(r[w]);
        total += n - c;
    }
    return total;
}

/* Degree-preserving 2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). */
static int try_switch(Mv *mv) {
    int a1 = listA[rnd_int(nA)];
    int a2 = listA[rnd_int(nA)];
    if (a1 == a2) return 0;
    int i = rnd_int(dg[a1]);
    int j = rnd_int(dg[a2]);
    int b1 = nb[a1 * DMAX + i];
    int b2 = nb[a2 * DMAX + j];
    if (b1 == b2) return 0;
    if (find_slot(a1, b2) >= 0) return 0;
    if (find_slot(a2, b1) >= 0) return 0;
    int k = find_slot(b2, a2);
    int l = find_slot(b1, a1);
    if (k < 0 || l < 0) return 0;
    nb[a1 * DMAX + i] = b2;
    nb[b2 * DMAX + k] = a1;
    nb[a2 * DMAX + j] = b1;
    nb[b1 * DMAX + l] = a2;
    mv->a1 = a1; mv->i = i; mv->b1 = b1;
    mv->a2 = a2; mv->j = j; mv->b2 = b2;
    mv->k = k; mv->l = l;
    return 1;
}

static void undo_switch(const Mv *m) {
    nb[m->a1 * DMAX + m->i] = m->b1;
    nb[m->b1 * DMAX + m->l] = m->a1;
    nb[m->a2 * DMAX + m->j] = m->b2;
    nb[m->b2 * DMAX + m->k] = m->a2;
}

/* Add vertices ap (side 0) and bp (side 1), then fill both to degree DEG.
   Each fill step removes an old edge (x,y) and adds (x,bp), (ap,y). */
static int grow_by_two(void) {
    if (n_cur + 2 > NCAP) return 0;
    int ap = n_cur, bp = n_cur + 1;
    col[ap] = 0; col[bp] = 1;
    dg[ap] = 0; dg[bp] = 0;
    listA[nA++] = ap;
    n_cur += 2;
    nb[ap * DMAX + dg[ap]++] = bp;
    nb[bp * DMAX + dg[bp]++] = ap;
    long guard = 0;
    while (dg[ap] < DEG) {
        if (++guard > 2000000) return 0;
        int x = listA[rnd_int(nA)];
        if (x == ap) continue;
        int i = rnd_int(dg[x]);
        int y = nb[x * DMAX + i];
        if (y == ap || y == bp) continue;
        if (find_slot(ap, y) >= 0) continue;
        if (find_slot(bp, x) >= 0) continue;
        int l = find_slot(y, x);
        if (l < 0) continue;
        nb[x * DMAX + i] = bp;
        nb[y * DMAX + l] = ap;
        nb[ap * DMAX + dg[ap]++] = y;
        nb[bp * DMAX + dg[bp]++] = x;
    }
    return 1;
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
    if (DEG < 1 || DEG > DMAX || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > NCAP - 2 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n0; v++) dg[v] = 0;
    int ok = 1;
    for (int e = 0; e < m0 && ok; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; break; }
        if (dg[u] >= DEG || dg[v] >= DEG) { ok = 0; break; }
        if (find_slot(u, v) >= 0) { ok = 0; break; }
        nb[u * DMAX + dg[u]++] = v;
        nb[v * DMAX + dg[v]++] = u;
    }
    if (ok)
        for (int v = 0; v < n0; v++)
            if (dg[v] != DEG) { ok = 0; break; }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    for (int v = 0; v < n0; v++) col[v] = -1;
    int bip = 1;
    for (int s = 0; s < n0 && bip; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue_[qt++] = s;
        while (qh < qt && bip) {
            int u = queue_[qh++];
            for (int i = 0; i < dg[u]; i++) {
                int w = nb[u * DMAX + i];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    queue_[qt++] = w;
                } else if (col[w] == col[u]) {
                    bip = 0;
                    break;
                }
            }
        }
    }
    if (!bip) {
        printf("0 0\n");
        return 0;
    }

    n_cur = n0;
    nA = 0;
    for (int v = 0; v < n0; v++)
        if (col[v] == 0) listA[nA++] = v;
    if (nA == 0 || eval_cost() != 0) {
        printf("0 0\n");
        return 0;
    }

    backup_n = n0;
    backup_nA = nA;
    memcpy(backup_nb, nb, sizeof(int) * (size_t)n0 * DMAX);

    while (elapsed() < DEADLINE) {
        n_cur = backup_n;
        nA = backup_nA;
        memcpy(nb, backup_nb, sizeof(int) * (size_t)backup_n * DMAX);
        for (int v = 0; v < backup_n; v++) dg[v] = DEG;
        if (!grow_by_two()) continue;

        long long cost = eval_cost();
        int ev = 0;
        while (cost > 0 && ev < ATT_EVALS && elapsed() < DEADLINE) {
            Mv mv;
            if (!try_switch(&mv)) continue;
            ev++;
            double temp = T_HI * (1.0 - (double)ev / ATT_EVALS) + T_LO;
            long long c2 = eval_cost();
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                undo_switch(&mv);
            }
        }
        if (cost == 0) {
            backup_n = n_cur;
            backup_nA = nA;
            memcpy(backup_nb, nb, sizeof(int) * (size_t)n_cur * DMAX);
        }
    }

    long long m = (long long)DEG * backup_nA;
    printf("%d %lld\n", backup_n, m);
    for (int a = 0; a < backup_nA; a++) {
        int v = listA[a];
        for (int i = 0; i < DEG; i++)
            printf("%d %d\n", v, backup_nb[v * DMAX + i]);
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


def _is_regular(n, edges, d):
    """True if every vertex 0..n-1 has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# Driver: baselines, then stage 1 (lift annealer), then stage 2 (edge-switch growth).
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

    remaining = 0.88 * time_limit - (time.monotonic() - start) - 3.0
    if remaining < 2.0:
        return best

    # Stage 1: lift annealer (parent engine). Gets the larger share.
    budget1 = 0.6 * remaining
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget1:.2f}", best_n],
                        timeout=budget1 + 8.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    # Stage 2: edge-switch growth from the best regular graph found so far.
    budget2 = 0.88 * time_limit - (time.monotonic() - start) - 2.5
    if budget2 >= 2.0 and _is_regular(best[0], best[1], d):
        try:
            out = lib.run_c(ANNEAL_SOURCE, [d, D, seed, f"{budget2:.2f}"],
                            stdin_graph=best, timeout=budget2 + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
