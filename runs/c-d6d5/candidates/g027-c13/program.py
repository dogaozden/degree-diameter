import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (lift annealer, unchanged from the parent): voltage lifts of
# semidirect products Z_m x| Z_k2 over a base of K A-vertices and K B-vertices,
# searched by simulated annealing with breakout weights and an elite pool.
# Kept as the first phase so the parent's best results are still produced.
# ----------------------------------------------------------------------------

LIFT_C = r"""
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
# Engine 2 (new, bold): direct annealing over simple d-regular bipartite graphs
# with degree-preserving double edge swaps. The objective is the number of
# ordered vertex pairs at distance > D, computed exactly with bitset BFS.
# Whenever the cost reaches 0, the graph is recorded and grown by two vertices
# (one per side) using d edge-splices, then annealing continues. This is not a
# voltage lift, so it can reach orders that lifts with small groups miss.
# ----------------------------------------------------------------------------

SWAP_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define DMAX 32
#define KMAX 1200
#define NMAX (2 * KMAX)
#define WMAX ((NMAX + 63) / 64)
#define RUN 20000
#define TSTART 3.0
#define TEND 0.2

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM;
static int nv, M;
static int adj[NMAX * DMAX];
static int ea[KMAX * DMAX], eb[KMAX * DMAX];
static int bestA[KMAX * DMAX], bestB[KMAX * DMAX];
static uint64_t BSA[NMAX * WMAX], BSB[NMAX * WMAX];
static int *tu, *tv, *fr;
static int cntd[NMAX], side[NMAX];
static int have_best = 0, bestnv = 0, bestM = 0;

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

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * DMAX;
    for (int i = 0; i < DEG; i++)
        if (p[i] == b) return 1;
    return 0;
}

static void replace_nb(int v, int old, int nw) {
    int *p = adj + (size_t)v * DMAX;
    for (int i = 0; i < DEG; i++)
        if (p[i] == old) { p[i] = nw; return; }
}

/* Edges (a1,b1),(a2,b2) become (a1,b2),(a2,b1). */
static void set_swap(int a1, int b1, int a2, int b2) {
    replace_nb(a1, b1, b2);
    replace_nb(b1, a1, a2);
    replace_nb(b2, a2, a1);
    replace_nb(a2, b2, b1);
}

/* Inverse of set_swap. */
static void unset_swap(int a1, int b1, int a2, int b2) {
    replace_nb(a1, b2, b1);
    replace_nb(b1, a2, a1);
    replace_nb(b2, a1, a2);
    replace_nb(a2, b1, b2);
}

/* Exact cost: number of ordered pairs at distance > DIAM (0 iff valid). */
static long long eval_cost(void) {
    int W = (nv + 63) >> 6;
    uint64_t *src_b = BSA, *dst_b = BSB;
    for (int v = 0; v < nv; v++) {
        uint64_t *row = src_b + (size_t)v * WMAX;
        for (int w = 0; w < W; w++) row[w] = 0;
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < nv; v++) {
            uint64_t *o = dst_b + (size_t)v * WMAX;
            const uint64_t *c = src_b + (size_t)v * WMAX;
            for (int w = 0; w < W; w++) o[w] = c[w];
            const int *av = adj + (size_t)v * DMAX;
            for (int i = 0; i < DEG; i++) {
                const uint64_t *cu = src_b + (size_t)av[i] * WMAX;
                for (int w = 0; w < W; w++) o[w] |= cu[w];
            }
        }
        uint64_t *tmp = src_b; src_b = dst_b; dst_b = tmp;
    }
    long long unc_total = 0;
    for (int v = 0; v < nv; v++) {
        const uint64_t *row = src_b + (size_t)v * WMAX;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc64(row[w]);
        unc_total += nv - pc;
    }
    return unc_total;
}

static void record_best(void) {
    if (!have_best || nv > bestnv) {
        have_best = 1;
        bestnv = nv;
        bestM = M;
        memcpy(bestA, ea, sizeof(int) * (size_t)M);
        memcpy(bestB, eb, sizeof(int) * (size_t)M);
    }
}

/* Splice d edges with distinct endpoints through two new vertices (one per side). */
static int grow(void) {
    if (nv + 2 > NMAX) return 0;
    int sel[DMAX];
    int ns = 0, tries = 0;
    while (ns < DEG && tries < 200000) {
        tries++;
        int e = rnd_int(M);
        int ok = 1;
        for (int j = 0; j < ns; j++)
            if (ea[sel[j]] == ea[e] || eb[sel[j]] == eb[e]) { ok = 0; break; }
        if (ok) sel[ns++] = e;
    }
    if (ns < DEG) return 0;
    int an = nv, bn = nv + 1;
    for (int i = 0; i < DEG; i++) {
        int e = sel[i];
        int a = ea[e], b = eb[e];
        replace_nb(a, b, bn);
        replace_nb(b, a, an);
        adj[(size_t)an * DMAX + i] = b;
        adj[(size_t)bn * DMAX + i] = a;
        ea[e] = an; eb[e] = b;
        ea[M + i] = a; eb[M + i] = bn;
    }
    M += DEG;
    nv += 2;
    return 1;
}

/* Random start: circulant with distinct shifts, K0 vertices per side (K0 >= DEG). */
static void random_init(int K0) {
    nv = 2 * K0;
    M = K0 * DEG;
    int sh[DMAX];
    int ns = 0;
    while (ns < DEG) {
        int s = rnd_int(K0);
        int ok = 1;
        for (int j = 0; j < ns; j++)
            if (sh[j] == s) { ok = 0; break; }
        if (ok) sh[ns++] = s;
    }
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K0; i++) {
            int e = l * K0 + i;
            int a = i, b = K0 + (i + sh[l]) % K0;
            ea[e] = a;
            eb[e] = b;
            adj[(size_t)a * DMAX + l] = b;
            adj[(size_t)b * DMAX + l] = a;
        }
    }
}

/* Load a simple, connected, d-regular bipartite graph from stdin ("n m" + edges). */
static int load_stdin(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 2 || n > NMAX || m <= 0 || m > KMAX * DMAX) return 0;
    if (2 * m != n * DEG) return 0;
    for (int i = 0; i < n; i++) cntd[i] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) return 0;
        if (cntd[u] >= DEG || cntd[v] >= DEG) return 0;
        tu[i] = u;
        tv[i] = v;
        adj[(size_t)u * DMAX + cntd[u]++] = v;
        adj[(size_t)v * DMAX + cntd[v]++] = u;
    }
    for (int i = 0; i < n; i++)
        if (cntd[i] != DEG) return 0;
    for (int i = 0; i < n; i++)
        for (int x = 0; x < DEG; x++)
            for (int y = x + 1; y < DEG; y++)
                if (adj[(size_t)i * DMAX + x] == adj[(size_t)i * DMAX + y]) return 0;
    for (int i = 0; i < n; i++) side[i] = -1;
    int head = 0, tail = 0;
    side[0] = 0;
    fr[tail++] = 0;
    while (head < tail) {
        int u = fr[head++];
        for (int x = 0; x < DEG; x++) {
            int v = adj[(size_t)u * DMAX + x];
            if (side[v] < 0) {
                side[v] = 1 - side[u];
                fr[tail++] = v;
            } else if (side[v] == side[u]) {
                return 0;
            }
        }
    }
    if (tail != n) return 0;
    for (int i = 0; i < m; i++) {
        if (side[tu[i]] == 0) { ea[i] = tu[i]; eb[i] = tv[i]; }
        else { ea[i] = tv[i]; eb[i] = tu[i]; }
    }
    M = m;
    nv = n;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_k]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int Kstart = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 1 || DEG > DMAX || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    tu = malloc(sizeof(int) * KMAX * DMAX);
    tv = malloc(sizeof(int) * KMAX * DMAX);
    fr = malloc(sizeof(int) * NMAX);
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    if (!load_stdin()) {
        int K0 = Kstart < DEG ? DEG : Kstart;
        if (K0 > KMAX) K0 = KMAX;
        random_init(K0);
    }

    long long cur = eval_cost();
    long long it = 0;
    while (elapsed() < DEADLINE) {
        if (cur == 0) {
            record_best();
            if (!grow()) break;
            cur = eval_cost();
            continue;
        }
        it++;
        double temp = TSTART * pow(TEND / TSTART, (double)(it % RUN) / (double)RUN);
        int e1 = rnd_int(M), e2 = rnd_int(M);
        if (e1 == e2) continue;
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        set_swap(a1, b1, a2, b2);
        eb[e1] = b2;
        eb[e2] = b1;
        long long c2 = eval_cost();
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
        } else {
            unset_swap(a1, b1, a2, b2);
            eb[e1] = b1;
            eb[e2] = b2;
        }
    }
    if (cur == 0) record_best();

    if (have_best) {
        printf("%d %d\n", bestnv, bestM);
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
# Driver: baselines, then phase 1 (lift annealer, the parent's search) and
# phase 2 (direct swap annealer started from the best graph so far).
# Every output is validated before it can replace the current best.
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

    avail = 0.90 * time_limit - (time.monotonic() - start) - 2.0
    if avail < 3.0:
        return best

    # Phase 1: the parent's lift annealer.
    b1 = 0.5 * avail
    try:
        out = lib.run_c(LIFT_C, [d, D, seed, f"{b1:.2f}", best_n], timeout=b1 + 3.0)
        consider(*lib.parse_graph_text(out))
    except Exception:
        pass

    # Phase 2: direct swap annealing with vertex growth, started from the best graph.
    b2 = 0.90 * time_limit - (time.monotonic() - start) - 1.0
    if b2 >= 3.0:
        try:
            out = lib.run_c(SWAP_C, [d, D, seed + 1, f"{b2:.2f}", 0],
                            stdin_graph=best, timeout=b2 + 3.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
