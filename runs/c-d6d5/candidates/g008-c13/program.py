import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Two-phase search for the target cases.
#
# Phase 1 (C_LIFT): the voltage-lift annealer from the previous version. It
# searches semidirect-product lifts for a large valid base graph.
#
# Phase 2 (C_GROW): a different search. It starts from the phase-1 graph and
# grows it by two vertices at a time. Growth removes d disjoint edges
# (a_i, b_i) and adds a new A-vertex joined to every b_i and a new B-vertex
# joined to every a_i, so all degrees stay d and the graph stays bipartite.
# Simulated annealing on bipartite 2-switches then repairs the diameter. The
# cost is the number of ordered vertex pairs at distance > D, computed with
# bitset BFS. A snapshot of the last valid graph is always kept, so a failed
# growth attempt is rolled back and the output is always valid.
# ----------------------------------------------------------------------------

C_LIFT = r"""
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


C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXGROW 400
#define ITERS_PER 20000
#define TEMP0 3.0
#define TEMP1 0.2
#define MAXFAIL 3000

static uint64_t rs[2];
static struct timespec TS0;
static double DEADLINE;
static int DEG, DIAM;
static int CAPV, CAPE, WMAX;
static int n0, n, m_e;
static int *deg, *adjl, *ex, *ey, *snx, *sny, *mark_a, *mark_b;
static unsigned char *adjm;
static uint64_t *bufA, *bufB;
static int snap_n, snap_m;
static int stamp_cur = 0;

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

static int rnd_int(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - TS0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - TS0.tv_nsec);
}

static int popc(uint64_t x) {
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_popcountll(x);
#else
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
#endif
}

static void add_nb(int v, int u) {
    adjl[(size_t)v * DEG + deg[v]] = u;
    deg[v]++;
}

static void remove_nb(int v, int u) {
    int *L = adjl + (size_t)v * DEG;
    for (int k = 0; k < deg[v]; k++) {
        if (L[k] == u) {
            L[k] = L[deg[v] - 1];
            deg[v]--;
            return;
        }
    }
}

static void replace_nb(int v, int oldu, int newu) {
    int *L = adjl + (size_t)v * DEG;
    for (int k = 0; k < deg[v]; k++) {
        if (L[k] == oldu) {
            L[k] = newu;
            return;
        }
    }
}

/* Adds edge (x in A, y in B). Caller guarantees it is new. */
static void add_edge(int x, int y) {
    add_nb(x, y);
    add_nb(y, x);
    adjm[(size_t)x * CAPV + y] = 1;
    adjm[(size_t)y * CAPV + x] = 1;
    ex[m_e] = x;
    ey[m_e] = y;
    m_e++;
}

static void remove_edge_pair(int a, int b) {
    int j = -1;
    for (int i = 0; i < m_e; i++) {
        if (ex[i] == a && ey[i] == b) { j = i; break; }
    }
    if (j < 0) return;
    remove_nb(a, b);
    remove_nb(b, a);
    adjm[(size_t)a * CAPV + b] = 0;
    adjm[(size_t)b * CAPV + a] = 0;
    m_e--;
    ex[j] = ex[m_e];
    ey[j] = ey[m_e];
}

static void rebuild_adj(void) {
    memset(deg, 0, sizeof(int) * (size_t)CAPV);
    for (int i = 0; i < CAPV; i++)
        memset(adjm + (size_t)i * CAPV, 0, (size_t)CAPV);
    for (int i = 0; i < m_e; i++) {
        int x = ex[i], y = ey[i];
        add_nb(x, y);
        add_nb(y, x);
        adjm[(size_t)x * CAPV + y] = 1;
        adjm[(size_t)y * CAPV + x] = 1;
    }
}

/* Exact count of ordered pairs at distance > DIAM, via bitset BFS. */
static long long eval_cost(void) {
    int W = (n + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur + (size_t)adjl[(size_t)v * DEG + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long cost = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[(size_t)v * W + w]);
        cost += n - c;
    }
    return cost;
}

/* Bipartite 2-switch on edges i=(a1,b1), j=(a2,b2) -> (a1,b2), (a2,b1).
   Applying it twice restores the original graph. */
static void do_switch(int i, int j) {
    int a1 = ex[i], b1 = ey[i], a2 = ex[j], b2 = ey[j];
    ey[i] = b2;
    ey[j] = b1;
    replace_nb(a1, b1, b2);
    replace_nb(b1, a1, a2);
    replace_nb(a2, b2, b1);
    replace_nb(b2, a2, a1);
    adjm[(size_t)a1 * CAPV + b1] = 0;
    adjm[(size_t)b1 * CAPV + a1] = 0;
    adjm[(size_t)a2 * CAPV + b2] = 0;
    adjm[(size_t)b2 * CAPV + a2] = 0;
    adjm[(size_t)a1 * CAPV + b2] = 1;
    adjm[(size_t)b2 * CAPV + a1] = 1;
    adjm[(size_t)a2 * CAPV + b1] = 1;
    adjm[(size_t)b1 * CAPV + a2] = 1;
}

/* Simulated annealing on 2-switches. Returns 1 when the cost reaches 0
   (state is then valid); otherwise returns 0 and the caller must restore. */
static int anneal(int iters) {
    long long c = eval_cost();
    if (c == 0) return 1;
    double ratio = TEMP1 / TEMP0;
    for (int it = 0; it < iters; it++) {
        if ((it & 127) == 0 && elapsed() > DEADLINE) return 0;
        double T = TEMP0 * pow(ratio, (double)it / (double)iters);
        int i = rnd_int(m_e), j = rnd_int(m_e);
        if (i == j) continue;
        int a1 = ex[i], b1 = ey[i], a2 = ex[j], b2 = ey[j];
        if (a1 == a2 || b1 == b2) continue;
        if (adjm[(size_t)a1 * CAPV + b2] || adjm[(size_t)a2 * CAPV + b1]) continue;
        do_switch(i, j);
        long long c2 = eval_cost();
        if (c2 <= c || rnd_unit() < exp(-(double)(c2 - c) / T)) {
            c = c2;
            if (c == 0) return 1;
        } else {
            do_switch(i, j);
        }
    }
    return 0;
}

static void save_snapshot(void) {
    snap_n = n;
    snap_m = m_e;
    memcpy(snx, ex, sizeof(int) * (size_t)m_e);
    memcpy(sny, ey, sizeof(int) * (size_t)m_e);
}

static void restore_snapshot(void) {
    n = snap_n;
    m_e = snap_m;
    memcpy(ex, snx, sizeof(int) * (size_t)m_e);
    memcpy(ey, sny, sizeof(int) * (size_t)m_e);
    rebuild_adj();
}

/* Add two vertices: new A-vertex na joined to b_1..b_DEG, new B-vertex nb joined
   to a_1..a_DEG, after removing the matching edges (a_k, b_k). Degrees stay DEG. */
static int grow_step(void) {
    int pa[16], pb[16];
    int cnt = 0;
    stamp_cur++;
    int tries = 0;
    while (cnt < DEG && tries < 100 * DEG + 1000) {
        tries++;
        int i = rnd_int(m_e);
        int a = ex[i], b = ey[i];
        if (mark_a[a] == stamp_cur || mark_b[b] == stamp_cur) continue;
        mark_a[a] = stamp_cur;
        mark_b[b] = stamp_cur;
        pa[cnt] = a;
        pb[cnt] = b;
        cnt++;
    }
    if (cnt < DEG) return 0;
    int na = n, nb = n + 1;
    n += 2;
    for (int k = 0; k < cnt; k++) remove_edge_pair(pa[k], pb[k]);
    for (int k = 0; k < cnt; k++) {
        add_edge(na, pb[k]);
        add_edge(pa[k], nb);
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit  (graph on stdin)\n");
        return 1;
    }
    timespec_get(&TS0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    uint64_t sm = sd * 2654435761ULL + 777ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    if (DEG < 1 || DEG > 16 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    int m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 <= 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)m0);
    int *evv = malloc(sizeof(int) * (size_t)m0);
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &evv[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }
    int *dg = calloc((size_t)n0, sizeof(int));
    int bad = 0;
    for (int i = 0; i < m0 && !bad; i++) {
        int u = eu[i], v = evv[i];
        if (u < 0 || u >= n0 || v < 0 || v >= n0 || u == v) { bad = 1; break; }
        dg[u]++;
        dg[v]++;
    }
    for (int v = 0; v < n0 && !bad; v++)
        if (dg[v] > DEG) bad = 1;
    if (bad) {
        printf("0 0\n");
        return 0;
    }
    /* Bipartition by BFS colouring. */
    int *ad = malloc(sizeof(int) * (size_t)n0 * DEG);
    int *fill = calloc((size_t)n0, sizeof(int));
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = evv[i];
        ad[(size_t)u * DEG + fill[u]++] = v;
        ad[(size_t)v * DEG + fill[v]++] = u;
    }
    int *col = malloc(sizeof(int) * (size_t)n0);
    int *qq = malloc(sizeof(int) * (size_t)n0);
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0 && !bad; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        qq[qt++] = s;
        while (qh < qt && !bad) {
            int u = qq[qh++];
            for (int k = 0; k < dg[u]; k++) {
                int v = ad[(size_t)u * DEG + k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    qq[qt++] = v;
                } else if (col[v] == col[u]) {
                    bad = 1;
                    break;
                }
            }
        }
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    CAPV = n0 + 2 * MAXGROW + 4;
    CAPE = CAPV * DEG;
    WMAX = (CAPV + 63) / 64;
    deg = calloc((size_t)CAPV, sizeof(int));
    adjl = malloc(sizeof(int) * (size_t)CAPV * DEG);
    adjm = calloc((size_t)CAPV * CAPV, 1);
    ex = malloc(sizeof(int) * (size_t)CAPE);
    ey = malloc(sizeof(int) * (size_t)CAPE);
    snx = malloc(sizeof(int) * (size_t)CAPE);
    sny = malloc(sizeof(int) * (size_t)CAPE);
    bufA = malloc(sizeof(uint64_t) * (size_t)CAPV * WMAX);
    bufB = malloc(sizeof(uint64_t) * (size_t)CAPV * WMAX);
    mark_a = calloc((size_t)CAPV, sizeof(int));
    mark_b = calloc((size_t)CAPV, sizeof(int));

    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = evv[i];
        if (col[u] == 0) { ex[i] = u; ey[i] = v; }
        else { ex[i] = v; ey[i] = u; }
    }
    n = n0;
    m_e = m0;
    rebuild_adj();

    if (eval_cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    save_snapshot();

    int fails = 0;
    while (elapsed() < DEADLINE && n + 2 <= n0 + 2 * MAXGROW && fails < MAXFAIL) {
        if (!grow_step()) {
            fails++;
            continue;
        }
        if (anneal(ITERS_PER)) {
            save_snapshot();
            fails = 0;
        } else {
            restore_snapshot();
            fails++;
        }
    }

    printf("%d %d\n", snap_n, snap_m);
    for (int i = 0; i < snap_m; i++)
        printf("%d %d\n", snx[i], sny[i]);
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
# Driver: baselines, then lift search (phase 1), then edge-switch growth (phase 2).
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

    budget_end = start + 0.86 * time_limit
    avail = budget_end - time.monotonic() - 2.0
    if avail < 2.0:
        return best

    # Phase 1: voltage-lift search for a large valid base graph.
    p1 = 0.55 * avail
    try:
        out = lib.run_c(C_LIFT, [d, D, seed, f"{p1:.2f}", best_n], timeout=p1 + 10.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    # Phase 2: grow the best valid graph by edge-switch annealing.
    p2 = budget_end - time.monotonic() - 1.5
    if p2 >= 2.0:
        try:
            out = lib.run_c(C_GROW, [d, D, seed, f"{p2:.2f}"], stdin_graph=best,
                            timeout=p2 + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
